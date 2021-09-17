#include "Optimizer.h"
#include <llvm/IR/DerivedTypes.h>
#include <llvm/IR/Intrinsics.h>
#include <llvm/ADT/SmallVector.h>
#include <llvm/ADT/StringExtras.h>
#include <llvm/IR/BasicBlock.h>
#include <llvm/IR/Constants.h>
#include <llvm/IR/Function.h>
#include <llvm/IR/IRBuilder.h>
#include <llvm/IR/Instructions.h>
#include <llvm/IR/IntrinsicInst.h>
#include <llvm/IR/LLVMContext.h>
#include <llvm/IR/Metadata.h>
#include <llvm/IR/Module.h>
#include <llvm/IR/Verifier.h>
#include <llvm/Support/FileSystem.h>
#include <llvm/Support/SourceMgr.h>
#include <llvm/Support/raw_ostream.h>

#include <llvm/Bitcode/BitcodeWriter.h>
#include <llvm/Support/ToolOutputFile.h>

#include <vector>
#include <iostream>
#include <sstream>

// We are avoiding the `getpid` name here to make sure we don't
// conflict with the (deprecated) getpid function from the Windows
// ucrt headers
std::uint32_t nativeGetProcessID(void) {
#ifdef _WIN32
	return 0;
#else
	return getpid();
#endif
}
extern "C" int CopyFileA(const char* existing_file_name,
	const char* new_file_name, int file_if_exists);

#ifdef _WIN32
void CopyFile(const std::string& from_path, const std::string& to_path) {
	if (CopyFileA(from_path.data(), to_path.data(), false) == 0) {
		std::cerr << "Unable to copy all data read from " << from_path << " to "
			<< to_path;
	}
}

#else
void CopyFile(const std::string& from_path, const std::string& to_path) {
	unlink(to_path.c_str());
	auto from_fd = open(from_path.c_str(), O_RDONLY);
	CHECK(-1 != from_fd) << "Unable to open source file " << from_path
		<< " for copying: " << strerror(errno);

	auto to_fd = open(to_path.c_str(), O_WRONLY | O_TRUNC | O_CREAT, 0666);
	CHECK(-1 != to_fd) << "Unable to open destination file " << to_path
		<< " for copying: " << strerror(errno);

	auto file_size = FileSize(from_path);
	int errno_copy = 0;

	do {
		auto num_read = read(from_fd, &(gCopyData[0]),
			std::min<size_t>(kCopyDataSize, file_size));
		if (-1 == num_read) {
			errno_copy = errno;
			break;
		}

		auto num_written =
			write(to_fd, &(gCopyData[0]), static_cast<size_t>(num_read));

		if (num_written != num_read) {
			errno_copy = errno;
			break;
		}

		file_size -= static_cast<size_t>(num_written);
	} while (file_size);

	close(from_fd);
	close(to_fd);

	if (errno_copy) {
		unlink(to_path.c_str());
		LOG(FATAL) << "Unable to copy all data read from " << from_path << " to "
			<< to_path << ": " << strerror(errno_copy);
	}
}
#endif

bool RenameFile(const std::string& from_path, const std::string& to_path) {
	auto ret = rename(from_path.c_str(), to_path.c_str());
	auto err = errno;
	if (-1 == ret) {
		std::cerr << "Unable to rename " << from_path << " to " << to_path << ": "
			<< strerror(err);
		return false;
	}
	else {
		return true;
	}
}

void RemoveFile(const std::string& path) {
	_unlink(path.c_str());
}

void MoveFile(const std::string& from_path, const std::string& to_path) {
	if (!RenameFile(from_path, to_path)) {
		CopyFile(from_path, to_path);
		RemoveFile(from_path);
	}
}



// Store an LLVM module into a file.
bool StoreModuleToFile(llvm::Module* module, std::string_view file_name,
	bool allow_failure) {
	//DLOG(INFO) << "Saving bitcode to file " << file_name;

	std::stringstream ss;
	ss << file_name << ".tmp." << nativeGetProcessID();
	auto tmp_name = ss.str();

	std::string error;
	llvm::raw_string_ostream error_stream(error);

	if (llvm::verifyModule(*module, &error_stream)) {
		error_stream.flush();
		std::cerr << "Error writing module to file " << file_name << ": " << error;
		return false;
	}

	std::error_code ec;
	llvm::ToolOutputFile bc(tmp_name.c_str(), ec, llvm::sys::fs::OF_None);

	if (!ec) std::cerr << "Unable to open output bitcode file for writing: " << tmp_name;


	llvm::WriteBitcodeToFile(*module, bc.os());

	bc.keep();
	if (!bc.os().has_error()) {
		std::string file_name_(file_name.data(), file_name.size());
		MoveFile(tmp_name, file_name_);
		return true;

	}
	else {
		RemoveFile(tmp_name);
		if (!allow_failure)
			std::cerr << "Error writing bitcode to file: " << file_name << ".";
		return false;
	}
}

// Store a module, serialized to LLVM IR, into a file.
bool StoreModuleIRToFile(llvm::Module* module, std::string_view file_name_,
	bool allow_failure) {
	std::string file_name(file_name_.data(), file_name_.size());
	std::error_code ec;
	llvm::raw_fd_ostream dest(file_name.c_str(), ec, llvm::sys::fs::F_Text);
	auto good = !ec;
	auto error = ec.message();

	if (!good) {
		if (!allow_failure)
			std::cerr << "Could not save LLVM IR to " << file_name << ": " << error;
		return false;
	}
	module->print(dest, nullptr);
	return true;
}


/*
 * Copyright (c) 2018 Trail of Bits, Inc.
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *     http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */


#pragma clang diagnostic push
#pragma clang diagnostic ignored "-Wsign-conversion"
#pragma clang diagnostic ignored "-Wconversion"
#pragma clang diagnostic ignored "-Wold-style-cast"
#pragma clang diagnostic ignored "-Wdocumentation"
#pragma clang diagnostic ignored "-Wswitch-enum"
#include <llvm/IR/Module.h>
#pragma clang diagnostic pop

#include <functional>
#include <initializer_list>
#include <map>
#include <memory>
#include <set>
#include <unordered_map>
#include <unordered_set>
#include <vector>









/*
 * Copyright (c) 2018 Trail of Bits, Inc.
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *     http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

#include <llvm/Transforms/IPO.h>
#include <llvm/Transforms/IPO/PassManagerBuilder.h>
#include <llvm/IR/LegacyPassManager.h>

#include "Version.h"
#include <llvm/ADT/Triple.h>
#include <llvm/IR/Constants.h>
#include <llvm/IR/DataLayout.h>
#include <llvm/IR/DebugInfo.h>
#include <llvm/IR/IRBuilder.h>
#include <llvm/IR/InstIterator.h>
#include <llvm/IR/LLVMContext.h>
#include <llvm/IR/LegacyPassManager.h>
#include <llvm/IR/MDBuilder.h>
#include <llvm/IR/Metadata.h>
#include <llvm/IR/Module.h>
#include <llvm/IR/Type.h>
#include <llvm/Transforms/IPO.h>
#include <llvm/Transforms/IPO/PassManagerBuilder.h>
#include <llvm/Transforms/Scalar.h>
#include <llvm/Transforms/Utils/Cloning.h>
#include <llvm/Transforms/Utils/Local.h>
#include <llvm/Transforms/Utils/ValueMapper.h>




namespace remill {

	void OptimizeModule(const remill::Arch* arch, llvm::Module* module,
		std::function<llvm::Function* (void)> generator,
		OptimizationGuide guide) {

		auto bb_func = BasicBlockFunction(module);
		auto slots = StateSlots(arch, module);

		llvm::legacy::FunctionPassManager func_manager(module);
		llvm::legacy::PassManager module_manager;

		auto TLI =
			new llvm::TargetLibraryInfoImpl(llvm::Triple(module->getTargetTriple()));

		TLI->disableAllFunctions();  // `-fno-builtin`.

		llvm::PassManagerBuilder builder;
		builder.OptLevel = 3;
		builder.SizeLevel = 0;
		builder.Inliner = llvm::createFunctionInliningPass(250);
		builder.LibraryInfo = TLI;  // Deleted by `llvm::~PassManagerBuilder`.
		builder.DisableUnrollLoops = false;  // Unroll loops!
		IF_LLVM_LT_900(builder.DisableUnitAtATime = false;)
		builder.RerollLoops = false;
		builder.SLPVectorize = guide.slp_vectorize;
		builder.LoopVectorize = guide.loop_vectorize;
		IF_LLVM_GTE_360(builder.VerifyInput = guide.verify_input;)
		IF_LLVM_GTE_360(builder.VerifyOutput = guide.verify_output;)

		// TODO(pag): Not sure when this became available.
		IF_LLVM_GTE_800(builder.MergeFunctions = false;)

		builder.populateFunctionPassManager(func_manager);
		builder.populateModulePassManager(module_manager);
		func_manager.doInitialization();
		llvm::Function* func = nullptr;
		while (nullptr != (func = generator())) {
			func_manager.run(*func);
		}
		func_manager.doFinalization();
		module_manager.run(*module);

		if (guide.eliminate_dead_stores) {
			RemoveDeadStores(arch, module, bb_func, slots);
		}
	}

	// Optimize a normal module. This might not contain special functions
	// like `__remill_basic_block`.
	//
	// NOTE(pag): It is an error to specify `guide.eliminate_dead_stores` as
	//            `true`.
	void OptimizeBareModule(llvm::Module* module, OptimizationGuide guide) {
		CHECK(!guide.eliminate_dead_stores);
		llvm::legacy::FunctionPassManager func_manager(module);
		llvm::legacy::PassManager module_manager;

		auto TLI =
			new llvm::TargetLibraryInfoImpl(llvm::Triple(module->getTargetTriple()));

		TLI->disableAllFunctions();  // `-fno-builtin`.

		llvm::PassManagerBuilder builder;
		builder.OptLevel = 3;
		builder.SizeLevel = 0;
		builder.Inliner = llvm::createFunctionInliningPass(250);
		builder.LibraryInfo = TLI;  // Deleted by `llvm::~PassManagerBuilder`.
		builder.DisableUnrollLoops = false;  // Unroll loops!
		IF_LLVM_LT_900(builder.DisableUnitAtATime = false;)
			builder.RerollLoops = false;
		builder.SLPVectorize = guide.slp_vectorize;
		builder.LoopVectorize = guide.loop_vectorize;
		IF_LLVM_GTE_360(builder.VerifyInput = guide.verify_input;)
		IF_LLVM_GTE_360(builder.VerifyOutput = guide.verify_output;)

		// TODO(pag): Not sure when this became available.
		IF_LLVM_GTE_800(builder.MergeFunctions = false;)

		builder.populateFunctionPassManager(func_manager);
		builder.populateModulePassManager(module_manager);
		func_manager.doInitialization();
		for (auto& func : *module) {
			func_manager.run(func);
		}
		func_manager.doFinalization();
		module_manager.run(*module);
	}

}  // namespace remill