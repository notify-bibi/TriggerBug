/*
 * Copyright (c) 2019 Trail of Bits, Inc.
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

#include "remill/Arch/Arch.h"

#include <glog/logging.h>

#include "Decode.h"
#include "remill/Arch/Instruction.h"
#include "remill/Arch/Name.h"
#include "remill/BC/ABI.h"
#include "remill/BC/Util.h"
#include "remill/OS/OS.h"

// clang-format off
#define ADDRESS_SIZE_BITS 64
#define INCLUDED_FROM_REMILL
#include "remill/Arch/SPARC64/Runtime/State.h"

// clang-format on

namespace remill {
namespace sparc {
namespace {
static const std::string_view kSPRegName = "sp";
static const std::string_view kPCRegName = "pc";
}  // namespace

class SPARC64Arch final : public Arch {
 public:
  SPARC64Arch(llvm::LLVMContext *context_, OSName os_name_, ArchName arch_name_)
      : Arch(context_, os_name_, arch_name_) {}

  virtual ~SPARC64Arch(void) = default;

  // Returns the name of the stack pointer register.
  std::string_view StackPointerRegisterName(void) const final {
    return kSPRegName;
  }

  // Returns the name of the program counter register.
  std::string_view ProgramCounterRegisterName(void) const final {
    return kPCRegName;
  }

  // Maximum number of bytes in an instruction.
  uint64_t MaxInstructionSize(void) const final {
    return 8;  // To handle `SET` idioms.
  }

  // Default calling convention for this architecture.
  llvm::CallingConv::ID DefaultCallingConv(void) const final {
    return llvm::CallingConv::C;
  }

  // Populate the `__remill_basic_block` function with variables.
  void PopulateBasicBlockFunction(llvm::Module *module,
                                  llvm::Function *bb_func) const override;

  llvm::Triple Triple(void) const final;
  llvm::DataLayout DataLayout(void) const final;

  // Decode an instruction.
  bool DecodeInstruction(uint64_t address, std::string_view instr_bytes,
                         Instruction &inst) const final;

  // Returns `true` if memory access are little endian byte ordered.
  bool MemoryAccessIsLittleEndian(void) const final {
    return false;
  }

  // Returns `true` if a given instruction might have a delay slot.
  bool MayHaveDelaySlot(const Instruction &inst) const final;

  // Returns `true` if we should lift the semantics of `next_inst` as a delay
  // slot of `inst`. The `branch_taken_path` tells us whether we are in the
  // context of the taken path of a branch or the not-taken path of a branch.
  virtual bool NextInstructionIsDelayed(const Instruction &inst,
                                        const Instruction &next_inst,
                                        bool branch_taken_path) const final;
};

// Populate the `__remill_basic_block` function with variables.
void SPARC64Arch::PopulateBasicBlockFunction(llvm::Module *module,
                                             llvm::Function *bb_func) const {

#define OFFSET_OF(type, access) \
  (reinterpret_cast<uintptr_t>(&reinterpret_cast<const volatile char &>( \
      static_cast<type *>(nullptr)->access)))

#define REG(name, access, type) \
  AddRegister(#name, type, OFFSET_OF(SPARCState, access), nullptr)

#define SUB_REG(name, access, type, parent_reg_name) \
  AddRegister(#name, type, OFFSET_OF(SPARCState, access), #parent_reg_name)

  auto &context = module->getContext();
  auto u8 = llvm::Type::getInt8Ty(context);
  auto u32 = llvm::Type::getInt32Ty(context);
  auto u64 = llvm::Type::getInt64Ty(context);
  auto u128 = llvm::Type::getInt128Ty(context);
  auto f32 = llvm::Type::getFloatTy(context);
  auto f64 = llvm::Type::getDoubleTy(context);

  auto zero_u8 = llvm::Constant::getNullValue(u8);
  auto zero_u32 = llvm::Constant::getNullValue(u32);
  auto zero_u64 = llvm::Constant::getNullValue(u64);

  const auto entry_block = &bb_func->getEntryBlock();
  llvm::IRBuilder<> ir(entry_block);

  REG(pc, pc.qword, u64);
  SUB_REG(PC, pc.qword, u64, pc);

  REG(npc, next_pc.qword, u64);
  SUB_REG(NEXT_PC, next_pc.qword, u64, npc);

  REG(sp, gpr.o6.qword, u64);
  SUB_REG(SP, gpr.o6.qword, u64, sp);

  REG(fp, gpr.i6.qword, u64);
  SUB_REG(FP, gpr.i6.qword, u64, fp);

  REG(i0, gpr.i0.qword, u64);
  REG(i1, gpr.i1.qword, u64);
  REG(i2, gpr.i2.qword, u64);
  REG(i3, gpr.i3.qword, u64);
  REG(i4, gpr.i4.qword, u64);
  REG(i5, gpr.i5.qword, u64);
  SUB_REG(i6, gpr.i6.qword, u64, fp);
  REG(i7, gpr.i7.qword, u64);
  REG(l0, gpr.l0.qword, u64);
  REG(l1, gpr.l1.qword, u64);
  REG(l2, gpr.l2.qword, u64);
  REG(l3, gpr.l3.qword, u64);
  REG(l4, gpr.l4.qword, u64);
  REG(l5, gpr.l5.qword, u64);
  REG(l6, gpr.l6.qword, u64);
  REG(l7, gpr.l7.qword, u64);
  REG(o0, gpr.o0.qword, u64);
  REG(o1, gpr.o1.qword, u64);
  REG(o2, gpr.o2.qword, u64);
  REG(o3, gpr.o3.qword, u64);
  REG(o4, gpr.o4.qword, u64);
  REG(o5, gpr.o5.qword, u64);
  SUB_REG(o6, gpr.o6.qword, u64, sp);
  REG(o7, gpr.o7.qword, u64);

  ir.CreateStore(zero_u64, ir.CreateAlloca(u64, nullptr, "g0"), false);
  ir.CreateStore(zero_u64, ir.CreateAlloca(u64, nullptr, "ignore_write_to_g0"),
                 false);

  REG(g1, gpr.g1.qword, u64);
  REG(g2, gpr.g2.qword, u64);
  REG(g3, gpr.g3.qword, u64);
  REG(g4, gpr.g4.qword, u64);
  REG(g5, gpr.g5.qword, u64);
  REG(g6, gpr.g6.qword, u64);
  REG(g7, gpr.g7.qword, u64);

  // Ancillary State Register
  REG(y, asr.yreg.qword, u64);
  REG(asi, asr.asi_flat, u64);
  REG(tick, asr.tick, u64);
  REG(fprs, asr.fprs_flat, u64);
  REG(gsr, asr.gsr.flat, u64);
  REG(softint, asr.softint, u64);
  REG(stick, asr.stick, u64);
  REG(stick_cmpr, asr.stick_cmpr, u64);
  REG(cfr, asr.cfr, u64);

  // this is for unknown asr to avoid crash.
  ir.CreateStore(zero_u64, ir.CreateAlloca(u64, nullptr, "asr"), false);

  REG(icc_c, asr.ccr.icc.c, u8);
  REG(icc_v, asr.ccr.icc.v, u8);
  REG(icc_z, asr.ccr.icc.z, u8);
  REG(icc_n, asr.ccr.icc.n, u8);

  REG(xcc_c, asr.ccr.xcc.c, u8);
  REG(xcc_v, asr.ccr.xcc.v, u8);
  REG(xcc_z, asr.ccr.xcc.z, u8);
  REG(xcc_n, asr.ccr.xcc.n, u8);

  REG(ccf_fcc0, fsr.fcc0, u8);
  REG(ccf_fcc1, fsr.fcc1, u8);
  REG(ccf_fcc2, fsr.fcc2, u8);
  REG(ccf_fcc3, fsr.fcc3, u8);

  REG(ccc, csr.ccc, u8);

  REG(fsr_aexc, fsr.aexc, u8);
  REG(fsr_cexc, fsr.cexc, u8);

  REG(v0, fpreg.v[0], u128);
  REG(v1, fpreg.v[1], u128);
  REG(v2, fpreg.v[2], u128);
  REG(v3, fpreg.v[3], u128);
  REG(v4, fpreg.v[4], u128);
  REG(v5, fpreg.v[5], u128);
  REG(v6, fpreg.v[6], u128);
  REG(v7, fpreg.v[7], u128);
  REG(v8, fpreg.v[8], u128);
  REG(v9, fpreg.v[9], u128);
  REG(v10, fpreg.v[10], u128);
  REG(v11, fpreg.v[11], u128);
  REG(v12, fpreg.v[12], u128);
  REG(v13, fpreg.v[13], u128);
  REG(v14, fpreg.v[14], u128);
  REG(v15, fpreg.v[15], u128);

  SUB_REG(f0, fpreg.v[0].floats.elems[0], f32, v0);
  SUB_REG(f1, fpreg.v[0].floats.elems[1], f32, v0);
  SUB_REG(f2, fpreg.v[0].floats.elems[2], f32, v0);
  SUB_REG(f3, fpreg.v[0].floats.elems[3], f32, v0);
  SUB_REG(f4, fpreg.v[1].floats.elems[0], f32, v1);
  SUB_REG(f5, fpreg.v[1].floats.elems[1], f32, v1);
  SUB_REG(f6, fpreg.v[1].floats.elems[2], f32, v1);
  SUB_REG(f7, fpreg.v[1].floats.elems[3], f32, v1);
  SUB_REG(f8, fpreg.v[2].floats.elems[0], f32, v2);
  SUB_REG(f9, fpreg.v[2].floats.elems[1], f32, v2);
  SUB_REG(f10, fpreg.v[2].floats.elems[2], f32, v2);
  SUB_REG(f11, fpreg.v[2].floats.elems[3], f32, v2);
  SUB_REG(f12, fpreg.v[3].floats.elems[0], f32, v3);
  SUB_REG(f13, fpreg.v[3].floats.elems[1], f32, v3);
  SUB_REG(f14, fpreg.v[3].floats.elems[2], f32, v3);
  SUB_REG(f15, fpreg.v[3].floats.elems[3], f32, v3);
  SUB_REG(f16, fpreg.v[4].floats.elems[0], f32, v4);
  SUB_REG(f17, fpreg.v[4].floats.elems[1], f32, v4);
  SUB_REG(f18, fpreg.v[4].floats.elems[2], f32, v4);
  SUB_REG(f19, fpreg.v[4].floats.elems[3], f32, v4);
  SUB_REG(f20, fpreg.v[5].floats.elems[0], f32, v5);
  SUB_REG(f21, fpreg.v[5].floats.elems[1], f32, v5);
  SUB_REG(f22, fpreg.v[5].floats.elems[2], f32, v5);
  SUB_REG(f23, fpreg.v[5].floats.elems[3], f32, v5);
  SUB_REG(f24, fpreg.v[6].floats.elems[0], f32, v6);
  SUB_REG(f25, fpreg.v[6].floats.elems[1], f32, v6);
  SUB_REG(f26, fpreg.v[6].floats.elems[2], f32, v6);
  SUB_REG(f27, fpreg.v[6].floats.elems[3], f32, v6);
  SUB_REG(f28, fpreg.v[7].floats.elems[0], f32, v7);
  SUB_REG(f29, fpreg.v[7].floats.elems[1], f32, v7);
  SUB_REG(f30, fpreg.v[7].floats.elems[2], f32, v7);
  SUB_REG(f31, fpreg.v[7].floats.elems[3], f32, v7);
  SUB_REG(f32, fpreg.v[8].floats.elems[0], f32, v8);
  SUB_REG(f33, fpreg.v[8].floats.elems[1], f32, v8);
  SUB_REG(f34, fpreg.v[8].floats.elems[2], f32, v8);
  SUB_REG(f35, fpreg.v[8].floats.elems[3], f32, v8);
  SUB_REG(f36, fpreg.v[9].floats.elems[0], f32, v9);
  SUB_REG(f37, fpreg.v[9].floats.elems[1], f32, v9);
  SUB_REG(f38, fpreg.v[9].floats.elems[2], f32, v9);
  SUB_REG(f39, fpreg.v[9].floats.elems[3], f32, v9);
  SUB_REG(f40, fpreg.v[10].floats.elems[0], f32, v10);
  SUB_REG(f41, fpreg.v[10].floats.elems[1], f32, v10);
  SUB_REG(f42, fpreg.v[10].floats.elems[2], f32, v10);
  SUB_REG(f43, fpreg.v[10].floats.elems[3], f32, v10);
  SUB_REG(f44, fpreg.v[11].floats.elems[0], f32, v11);
  SUB_REG(f45, fpreg.v[11].floats.elems[1], f32, v11);
  SUB_REG(f46, fpreg.v[11].floats.elems[2], f32, v11);
  SUB_REG(f47, fpreg.v[11].floats.elems[3], f32, v11);
  SUB_REG(f48, fpreg.v[12].floats.elems[0], f32, v12);
  SUB_REG(f49, fpreg.v[12].floats.elems[1], f32, v12);
  SUB_REG(f50, fpreg.v[12].floats.elems[2], f32, v12);
  SUB_REG(f51, fpreg.v[12].floats.elems[3], f32, v12);
  SUB_REG(f52, fpreg.v[13].floats.elems[0], f32, v13);
  SUB_REG(f53, fpreg.v[13].floats.elems[1], f32, v13);
  SUB_REG(f54, fpreg.v[13].floats.elems[2], f32, v13);
  SUB_REG(f55, fpreg.v[13].floats.elems[3], f32, v13);
  SUB_REG(f56, fpreg.v[14].floats.elems[0], f32, v14);
  SUB_REG(f57, fpreg.v[14].floats.elems[1], f32, v14);
  SUB_REG(f58, fpreg.v[14].floats.elems[2], f32, v14);
  SUB_REG(f59, fpreg.v[14].floats.elems[3], f32, v14);
  SUB_REG(f60, fpreg.v[15].floats.elems[0], f32, v15);
  SUB_REG(f61, fpreg.v[15].floats.elems[1], f32, v15);
  SUB_REG(f62, fpreg.v[15].floats.elems[2], f32, v15);
  SUB_REG(f63, fpreg.v[15].floats.elems[3], f32, v15);

  SUB_REG(d0, fpreg.v[0].doubles.elems[0], f64, v0);
  SUB_REG(d2, fpreg.v[0].doubles.elems[1], f64, v0);
  SUB_REG(d4, fpreg.v[1].doubles.elems[0], f64, v1);
  SUB_REG(d6, fpreg.v[1].doubles.elems[1], f64, v1);
  SUB_REG(d8, fpreg.v[2].doubles.elems[0], f64, v2);
  SUB_REG(d10, fpreg.v[2].doubles.elems[1], f64, v2);
  SUB_REG(d12, fpreg.v[3].doubles.elems[0], f64, v3);
  SUB_REG(d14, fpreg.v[3].doubles.elems[1], f64, v3);
  SUB_REG(d16, fpreg.v[4].doubles.elems[0], f64, v4);
  SUB_REG(d18, fpreg.v[4].doubles.elems[1], f64, v4);
  SUB_REG(d20, fpreg.v[5].doubles.elems[0], f64, v5);
  SUB_REG(d22, fpreg.v[5].doubles.elems[1], f64, v5);
  SUB_REG(d24, fpreg.v[6].doubles.elems[0], f64, v6);
  SUB_REG(d26, fpreg.v[6].doubles.elems[1], f64, v6);
  SUB_REG(d28, fpreg.v[7].doubles.elems[0], f64, v7);
  SUB_REG(d30, fpreg.v[7].doubles.elems[1], f64, v7);
  SUB_REG(d32, fpreg.v[8].doubles.elems[0], f64, v8);
  SUB_REG(d34, fpreg.v[8].doubles.elems[1], f64, v8);
  SUB_REG(d36, fpreg.v[9].doubles.elems[0], f64, v9);
  SUB_REG(d38, fpreg.v[9].doubles.elems[1], f64, v9);
  SUB_REG(d40, fpreg.v[10].doubles.elems[0], f64, v10);
  SUB_REG(d42, fpreg.v[10].doubles.elems[1], f64, v10);
  SUB_REG(d44, fpreg.v[11].doubles.elems[0], f64, v11);
  SUB_REG(d46, fpreg.v[11].doubles.elems[1], f64, v11);
  SUB_REG(d48, fpreg.v[12].doubles.elems[0], f64, v12);
  SUB_REG(d50, fpreg.v[12].doubles.elems[1], f64, v12);
  SUB_REG(d52, fpreg.v[13].doubles.elems[0], f64, v13);
  SUB_REG(d54, fpreg.v[13].doubles.elems[1], f64, v13);
  SUB_REG(d56, fpreg.v[14].doubles.elems[0], f64, v14);
  SUB_REG(d58, fpreg.v[14].doubles.elems[1], f64, v14);
  SUB_REG(d60, fpreg.v[15].doubles.elems[0], f64, v15);
  SUB_REG(d62, fpreg.v[15].doubles.elems[1], f64, v15);

  // NOTE(pag): This is a bit of a lie, but kind of like in x87 with 80-bit
  //            extended precision, we treat quad precision floats as being
  //            doubles.
  SUB_REG(q0, fpreg.v[0].doubles.elems[0], f64, v0);
  SUB_REG(q4, fpreg.v[1].doubles.elems[0], f64, v1);
  SUB_REG(q8, fpreg.v[2].doubles.elems[0], f64, v2);
  SUB_REG(q12, fpreg.v[3].doubles.elems[0], f64, v3);
  SUB_REG(q16, fpreg.v[4].doubles.elems[0], f64, v4);
  SUB_REG(q20, fpreg.v[5].doubles.elems[0], f64, v5);
  SUB_REG(q24, fpreg.v[6].doubles.elems[0], f64, v6);
  SUB_REG(q28, fpreg.v[7].doubles.elems[0], f64, v7);
  SUB_REG(q32, fpreg.v[8].doubles.elems[0], f64, v8);
  SUB_REG(q36, fpreg.v[9].doubles.elems[0], f64, v9);
  SUB_REG(q40, fpreg.v[10].doubles.elems[0], f64, v10);
  SUB_REG(q44, fpreg.v[11].doubles.elems[0], f64, v11);
  SUB_REG(q48, fpreg.v[12].doubles.elems[0], f64, v12);
  SUB_REG(q52, fpreg.v[13].doubles.elems[0], f64, v13);
  SUB_REG(q56, fpreg.v[14].doubles.elems[0], f64, v14);
  SUB_REG(q60, fpreg.v[15].doubles.elems[0], f64, v15);

  // NOTE(pag): Passing `nullptr` as the type will force `Arch::AddRegister`
  //            to infer the type based on what it finds. It's a pointer to
  //            a structure type, so we can check that.
  const auto prev_window_link = REG(PREV_WINDOW_LINK, window, nullptr);
  CHECK(prev_window_link->type->isPointerTy());
  const auto window_type = prev_window_link->type->getPointerElementType();
  CHECK(window_type->isStructTy());

  auto window = ir.CreateAlloca(window_type, nullptr, "WINDOW");
  ir.CreateAlloca(prev_window_link->type, nullptr, "PREV_WINDOW");

  // `WINDOW_LINK = &(WINDOW->prev_window);`
  llvm::Value *gep_indexes[2] = {zero_u32, llvm::ConstantInt::get(u32, 33)};
  auto window_link =
      ir.CreateInBoundsGEP(window_type, window, gep_indexes, "WINDOW_LINK");
  auto nullptr_window = llvm::Constant::getNullValue(prev_window_link->type);
  ir.CreateStore(nullptr_window, window_link, false);

  ir.CreateStore(zero_u8, ir.CreateAlloca(u8, nullptr, "IGNORE_BRANCH_TAKEN"),
                 false);
  ir.CreateStore(zero_u64, ir.CreateAlloca(u64, nullptr, "IGNORE_PC"), false);
  ir.CreateStore(zero_u64, ir.CreateAlloca(u64, nullptr, "IGNORE_NEXT_PC"),
                 false);
  ir.CreateStore(zero_u64, ir.CreateAlloca(u64, nullptr, "IGNORE_RETURN_PC"),
                 false);

  const auto pc_arg = NthArgument(bb_func, kPCArgNum);
  const auto state_ptr_arg = NthArgument(bb_func, kStatePointerArgNum);

  (void) RegisterByName(kNextPCVariableName)->AddressOf(state_ptr_arg, ir);

  ir.CreateStore(pc_arg,
                 RegisterByName(kPCVariableName)->AddressOf(state_ptr_arg, ir),
                 false);
}

llvm::Triple SPARC64Arch::Triple(void) const {
  auto triple = BasicTriple();
  triple.setArch(llvm::Triple::sparcv9);
  return triple;
}

llvm::DataLayout SPARC64Arch::DataLayout(void) const {
  return llvm::DataLayout("E-m:e-i64:64-n32:64-S128");
}

// Returns `true` if a given instruction might have a delay slot.
bool SPARC64Arch::MayHaveDelaySlot(const Instruction &inst) const {
  return inst.has_branch_taken_delay_slot ||
         inst.has_branch_not_taken_delay_slot;
}

// Returns `true` if we should lift the semantics of `next_inst` as a delay
// slot of `inst`. The `branch_taken_path` tells us whether we are in the
// context of the taken path of a branch or the not-taken path of a branch.
bool SPARC64Arch::NextInstructionIsDelayed(const Instruction &inst,
                                           const Instruction &next_inst,
                                           bool branch_taken_path) const {
  if (inst.delayed_pc != next_inst.pc) {
    return false;
  }

  if (branch_taken_path) {
    return inst.has_branch_taken_delay_slot;
  } else {
    return inst.has_branch_not_taken_delay_slot;
  }
}

// Decode an instruction.
bool SPARC64Arch::DecodeInstruction(uint64_t address,
                                    std::string_view inst_bytes,
                                    Instruction &inst) const {

  inst.pc = address;
  inst.arch_name = arch_name;
  inst.arch = this;
  inst.category = Instruction::kCategoryInvalid;
  inst.operands.clear();
  inst.next_pc = address + inst_bytes.size();  // Default fall-through.
  inst.branch_taken_pc = 0;
  inst.branch_not_taken_pc = 0;
  inst.has_branch_taken_delay_slot = false;
  inst.has_branch_not_taken_delay_slot = false;

  if (address % 4) {
    return false;
  }

  if (inst_bytes.size() != 4 && inst_bytes.size() != 8) {
    return false;
  }

  if (!inst.bytes.empty() && inst.bytes.data() == inst_bytes.data()) {
    inst.bytes.resize(inst_bytes.size());
  } else {
    inst.bytes = inst_bytes;
  }

  if (!sparc64::TryDecode(inst)) {
    inst.category = Instruction::kCategoryInvalid;
    inst.operands.clear();
    LOG(ERROR) << "Unable to decode: " << inst.Serialize();
    return false;
  }

  return inst.IsValid();
}

}  // namespace sparc

Arch::ArchPtr Arch::GetSPARC64(llvm::LLVMContext *context_, OSName os_name_,
                               ArchName arch_name_) {
  if (arch_name_ == kArchSparc64) {
    return std::make_unique<sparc::SPARC64Arch>(context_, os_name_, arch_name_);

  } else {
    LOG(FATAL) << "Invalid arch name passed to Arch::GetSPARC::"
               << GetArchName(arch_name_);
    return {};
  }
}

}  // namespace remill
