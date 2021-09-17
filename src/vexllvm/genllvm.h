#ifndef GENLLVM_H
#define GENLLVM_H

#include <llvm/IR/DerivedTypes.h>
#include <llvm/IR/LLVMContext.h>
#include <llvm/IR/Module.h>
#include <llvm/IR/IRBuilder.h>

extern "C" {
#include <libvex.h>
#include <libvex_ir.h>
}

#include <string>
#include <map>
#include <stdint.h>

class Guest;
#define SCALABLE false
struct guest_ctx_field;

class GenLLVM
{
public:
	GenLLVM(const Guest& gs, const char* modname = "vexllvm");
	virtual ~GenLLVM(void) {}

	llvm::IRBuilder<>* getBuilder(void) { return builder.get(); }
	llvm::Module& getModule(void) { return *mod; }
	std::unique_ptr<llvm::Module> takeModule(const char* new_name = nullptr);

	static llvm::Type* vexTy2LLVM(IRType ty);
	static std::unique_ptr<GenLLVM>& getGenLLVM();
	
	llvm::Value* readCtx(unsigned int byteOff, IRType ty);
	llvm::Value* readCtx(
		unsigned int byteOff, int bias, int len, llvm::Value* ix,
		llvm::Type* t);
	llvm::Value* writeCtx(unsigned int byteOff, llvm::Value* v);
	llvm::Value* writeCtx(
		unsigned int byteOff, int bias, int len,
		llvm::Value* ix, llvm::Value* v);
	llvm::Value* getCtxByteGEP(unsigned int byteOff, llvm::Type* ty);
	llvm::Value* getCtxTyGEP(llvm::Value* tyOff, llvm::Type* ty);
	llvm::Value* getCtxBase(void) const { return cur_guest_ctx; }

	void markLinked();
	llvm::Value* getLinked();
	
	void store(llvm::Value* addr, llvm::Value* data);
	llvm::Value* load(llvm::Value* addr_v, IRType vex_type);
	llvm::Value* load(llvm::Value* addr_v, llvm::Type* ty);
	void beginBB(const char* name);
	llvm::Function* endBB(llvm::Value*);
	void setExitType(uint8_t exit_type);
	llvm::Value* to16x8i(llvm::Value*) const;
	llvm::Value* to32x8i(llvm::Value*) const;
	void memFence(void);
	void setFakeSysReads(void) { fake_vsys_reads = true; }

	void setUseReloc(bool v) { use_reloc = v; }

	static llvm::LLVMContext& getContext() { return llvm_ctx; }
	void mkFuncTy(unsigned N);
private:
	llvm::Type* getGuestTy(void);

	const Guest		&guest;
	llvm::Type		*guestCtxTy;

	std::unique_ptr<llvm::IRBuilder<>> builder;
	std::unique_ptr<llvm::Module>	mod;
	llvm::FunctionType		*funcTy;

	/* current state data */
	typedef std::map<
		std::pair<unsigned /*off */, unsigned /* bytes */>,
		llvm::Value*
		> gepbyte_map_t;
	typedef std::map<llvm::Type*, llvm::Value*> ctxcast_map_t;

	gepbyte_map_t		gepbyte_map;
	ctxcast_map_t		ctxcast_map;

	llvm::Value*		cur_guest_ctx;
	llvm::Value*		cur_memory_log;
	unsigned int		memlog_slot;

	llvm::Function*		cur_f;
	llvm::BasicBlock*	entry_bb;
	bool			log_last_store;

	bool			fake_vsys_reads;
	bool			use_reloc;

	static unsigned int	mod_c;

	static llvm::LLVMContext	llvm_ctx;
};

llvm::LLVMContext& getGlobalContext();

// Store an LLVM module into a file.
bool StoreModuleToFile(llvm::Module* module, std::string_view file_name, bool allow_failure);
// Store a module, serialized to LLVM IR, into a file.
bool StoreModuleIRToFile(llvm::Module* module, std::string_view file_name_, bool allow_failure);
extern std::unique_ptr<GenLLVM> theGenLLVM;

#endif