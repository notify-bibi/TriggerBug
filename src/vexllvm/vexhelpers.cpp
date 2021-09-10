#include <llvm/IR/Module.h>
#include <llvm/IR/Instructions.h>

#include <llvm/IRReader/IRReader.h>
#include <llvm/Support/SourceMgr.h>
#include <llvm/Transforms/Utils/Cloning.h>

#include <iostream>
#include <stdio.h>
#include "Sugar.h"
#include "genllvm.h"

//#include "jitengine.h"
#include "vexhelpers.h"

#define VEXOP_BC_FILE "vexops.bc"

using namespace llvm;

std::unique_ptr<VexHelpers> theVexHelpers;
extern void vexop_setup_fp(VexHelpers* vh);

VexHelpers::VexHelpers(): ext_mod(nullptr), m_arch(VexArch_INVALID)
{
	/* env not set => assume running from git root */
	bc_dirpath = getenv("VEXLLVM_HELPER_PATH");
	if (bc_dirpath == nullptr || strlen(bc_dirpath) == 0) {
#ifdef VEXLLVM_HELPER_PATH
		if (strlen(VEXLLVM_HELPER_PATH)) {
			bc_dirpath = VEXLLVM_HELPER_PATH;
	    }
		else {
			bc_dirpath = "bitcode";
		}
#else
		bc_dirpath = "bitcode";
#endif
	}
}

void VexHelpers::loadDefaultModules(Arch::Arch arch)
{
	if (m_arch == arch) {
		return;
	}
	m_arch = arch;
	char		path_buf[512];

	const char* helper_file = nullptr;
	switch(arch) {
	case VexArchAMD64: helper_file = "libvex_amd64_helpers.bc"; break;
	case VexArchX86: helper_file = "libvex_x86_helpers.bc"; break;
	case VexArchARM: helper_file = "libvex_arm_helpers.bc"; break;
	case VexArchMIPS32: break; /* no useful helpers for mips */
	default:
		assert(!"known arch for helpers");
	}

	if (helper_file) {
		snprintf(path_buf, 512, "%s/%s", bc_dirpath, helper_file);
		helper_mod = loadMod(path_buf);
	}

	snprintf(path_buf, 512, "%s/%s", bc_dirpath, VEXOP_BC_FILE);
	vexop_mod = loadMod(path_buf);

	vexop_setup_fp(this);

	assert (vexop_mod && (helper_file == nullptr || helper_mod));
}

std::unique_ptr<VexHelpers> VexHelpers::create(Arch::Arch arch)
{
	auto vh = new VexHelpers();
	vh->loadDefaultModules(arch);
	return std::unique_ptr<VexHelpers>(vh);
}

std::unique_ptr<VexHelpers>& VexHelpers::getVexHelpers()
{
	return theVexHelpers;
}

std::unique_ptr<Module> VexHelpers::loadMod(const char* path)
{ return loadModFromPath(path); }

std::unique_ptr<Module> VexHelpers::loadModFromPath(const char* path)
{
	SMDiagnostic	diag;	
	auto ret_mod = llvm::parseIRFile(path, diag, getGlobalContext());
	if (ret_mod == nullptr) {
		std::string	s(diag.getMessage());
		std::cerr
			<< "Error Parsing Bitcode File '"
			<< path << "': " << s << '\n';
	}
	assert (ret_mod && "Couldn't parse bitcode mod");
	auto err = ret_mod->materializeAll();
	if (err) {
		std::cerr << "Materialize failed... " << std::endl;
		assert (0 == 1 && "BAD MOD");
	}
	return ret_mod;
}

umod_list VexHelpers::takeModules(void)
{
	umod_list	l;
	while (!user_mods.empty()) {
		auto m = (user_mods.front()).release();
		user_mods.pop_front();
		l.emplace_back(m);
	}
	if (helper_mod) l.emplace_back(std::move(helper_mod));
	l.emplace_back(std::move(vexop_mod));
	return l;
}

void VexHelpers::loadUserMod(const char* path)
{
	char	pathbuf[512];

	assert ((strlen(path)+strlen(bc_dirpath)) < 512);
	snprintf(pathbuf, 512, "%s/%s", bc_dirpath, path);

	auto m = loadMod(pathbuf);
	assert (m != nullptr && "Could not load user module");
	user_mods.push_back(std::move(m));
}

void VexHelpers::destroyMods(void)
{
	helper_mod = nullptr;
	vexop_mod = nullptr;
	user_mods.clear();
}

VexHelpers::~VexHelpers()
{
	destroyMods();
}

Function* VexHelpers::getCallHelper(const char* s)
{
	auto &mod = theGenLLVM->getModule();
	auto in_mod_f = mod.getFunction(s);
	if (!in_mod_f) {
		auto f = getHelper(s);
		if (!f) {
			return nullptr;
		}
		in_mod_f = Function::Create(
			f->getFunctionType(),
			Function::ExternalLinkage,
			s,
			mod);
	}
	return in_mod_f;
}

Function* VexHelpers::getHelper(const char* s) const
{
	Function	*f;

	if (ext_mod) {
		return ext_mod->getFunction(s);
	}

	/* TODO why not start using a better algorithm sometime */
	if (helper_mod && (f = helper_mod->getFunction(s))) return f;

	assert (vexop_mod);
	if ((f = vexop_mod->getFunction(s))) return f;

	for (auto &m : user_mods) {
		if ((f = m->getFunction(s)))
			return f;
	}

	return nullptr;
}

void VexHelpers::moveToJITEngine(JITEngine& je)
{
	//if (helper_mod)
	//	je.moveModule(
	//		std::unique_ptr<Module>(
	//			CloneModule(*helper_mod)));
	//if (vexop_mod)
	//	je.moveModule(
	//		std::unique_ptr<Module>(
	//			CloneModule(*vexop_mod)));
}

std::unique_ptr<llvm::Module> VexHelperDummy::loadMod(const char* path)
{
	fprintf(stderr, "FAILING LOAD MOD %s\n", path);
	return nullptr;
}

void VexHelpers::useExternalMod(Module* m)
{
	assert (ext_mod == nullptr);
	destroyMods();
	ext_mod = m;
}
