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

#include <glog/logging.h>
#include <remill/BC/ABI.h>

#include <bitset>

#include "Decode.h"

using namespace remill::sparc;

namespace remill {
namespace sparc32 {
namespace {

static constexpr unsigned kAddressSize = 32;

static const std::string_view kCondBrName[1U << 4U] = {
    [0b0000] = "N",   [0b0001] = "123", [0b0010] = "12",  [0b0011] = "13",
    [0b0100] = "1",   [0b0101] = "23",  [0b0110] = "2",   [0b0111] = "3",
    [0b1000] = "A",   [0b1001] = "0",   [0b1010] = "03",  [0b1011] = "02",
    [0b1100] = "023", [0b1101] = "01",  [0b1110] = "013", [0b1111] = "012"};

static const std::string_view kFpuRegName_fN[] = {
    "f0",  "f1",  "f2",  "f3",  "f4",  "f5",  "f6",  "f7",  "f8",  "f9",  "f10",
    "f11", "f12", "f13", "f14", "f15", "f16", "f17", "f18", "f19", "f20", "f21",
    "f22", "f23", "f24", "f25", "f26", "f27", "f28", "f29", "f30", "f31",
};

static void AddBranchTaken(Instruction &inst) {
  if (!inst.in_delay_slot) {
    AddDestRegop(inst, "BRANCH_TAKEN", 8);
  } else {
    AddDestRegop(inst, "IGNORE_BRANCH_TAKEN", 8);
  }
}

static void AddPCDest(Instruction &inst) {
  if (!inst.in_delay_slot) {
    AddDestRegop(inst, "PC", kAddressSize);
  } else {
    AddDestRegop(inst, "IGNORE_PC", kAddressSize);
  }
}

static void AddNPCDest(Instruction &inst) {
  if (!inst.in_delay_slot) {
    AddDestRegop(inst, "NEXT_PC", kAddressSize);
  } else {
    AddDestRegop(inst, "IGNORE_NEXT_PC", kAddressSize);
  }
}

static void AddReturnPCDest(Instruction &inst) {
  if (!inst.in_delay_slot) {
    AddDestRegop(inst, "RETURN_PC", kAddressSize);
  } else {
    AddDestRegop(inst, "IGNORE_RETURN_PC", kAddressSize);
  }
}

static void AddIntRegop(Instruction &inst, unsigned index, unsigned size,
                        Operand::Action action) {
  inst.operands.emplace_back();
  auto &op = inst.operands.back();
  op.type = Operand::kTypeRegister;
  op.size = size;
  op.action = action;
  op.reg.size = size;
  if (Operand::kActionRead == action) {
    if (!index) {
      op.type = Operand::kTypeImmediate;
      op.imm.is_signed = false;
      op.imm.val = 0;
    } else {
      op.reg.name = kReadIntRegName[index];
    }
  } else {
    op.reg.name = kWriteIntRegName[index];
  }
}

static bool AddFpuRegOp(Instruction &inst, unsigned index, unsigned size,
                        Operand::Action action) {

  inst.operands.emplace_back();
  auto &op = inst.operands.back();
  op.type = Operand::kTypeRegister;
  op.size = size;
  op.action = action;
  op.reg.size = size;

  if (op.reg.size == 32) {
    op.reg.name = kFpuRegName_fN[index];

  } else if (size == 64) {
    if (index & 1) {
      return false;  // Low order bit, `bit<5>`, must be 0 in sparcv8.
    }
    op.reg.name = kFpuRegName_fN[index];
    op.reg.name[0] = 'd';

  } else if (size == 128) {

    // Low order bit, `bit<5>`, must be 0 in sparcv8, and the second lowest
    // order bit must also be zero.
    if (index & 2) {
      return false;
    }
    op.reg.name = kFpuRegName_fN[index];
    op.reg.name[0] = 'q';

  } else {
    return false;
  }

  return true;
}

static void AddPCRelop(Instruction &inst, int64_t disp) {
  inst.operands.emplace_back();
  auto &op = inst.operands.back();
  op.type = Operand::kTypeAddress;
  op.size = kAddressSize;
  op.action = Operand::kActionRead;
  op.addr.kind = Operand::Address::kControlFlowTarget;
  op.addr.address_size = kAddressSize;
  op.addr.base_reg.name = "PC";
  op.addr.base_reg.size = kAddressSize;
  op.addr.displacement = disp;
}

static void AddNextPCRelop(Instruction &inst, int64_t disp) {
  inst.operands.emplace_back();
  auto &op = inst.operands.back();
  op.type = Operand::kTypeAddress;
  op.size = kAddressSize;
  op.action = Operand::kActionRead;
  op.addr.kind = Operand::Address::kControlFlowTarget;
  op.addr.address_size = kAddressSize;
  op.addr.base_reg.name = "NEXT_PC";
  op.addr.base_reg.size = kAddressSize;
  op.addr.displacement = disp;
}

static void AddBasePlusOffsetMemop(Instruction &inst, Operand::Action action,
                                   uint32_t access_size, uint32_t base_reg,
                                   uint32_t index_reg, int64_t disp) {
  inst.operands.emplace_back();
  auto &op = inst.operands.back();
  op.type = Operand::kTypeAddress;
  op.size = access_size;
  op.action = action;

  op.addr.kind = action == Operand::kActionRead
                     ? Operand::Address::kMemoryRead
                     : Operand::Address::kMemoryWrite;
  op.addr.address_size = kAddressSize;

  if (base_reg && index_reg) {
    op.addr.base_reg.name = kReadIntRegName[base_reg];
    op.addr.base_reg.size = kAddressSize;

    op.addr.index_reg.name = kReadIntRegName[index_reg];
    op.addr.index_reg.size = kAddressSize;
    op.addr.scale = 1;

  } else if (base_reg) {
    op.addr.base_reg.name = kReadIntRegName[base_reg];
    op.addr.base_reg.size = kAddressSize;

  } else if (index_reg) {
    op.addr.base_reg.name = kReadIntRegName[index_reg];
    op.addr.base_reg.size = kAddressSize;
  }

  op.addr.displacement = disp;
}

static bool TryDecodeRDasr(Instruction &inst, uint32_t bits) {
  Format3 enc = {bits};
  inst.category = Instruction::kCategoryNormal;
  switch (enc.rs1) {
    case 0:  // rd %y, rd
      inst.function = "RDY";
      break;
    case 2:  // rd %ccr, rd
      inst.function = "RDCCR";
      break;
    case 3:  // rd %asi, rd
      inst.function = "RDASI";
      break;
    case 4:  // rd %tick, rd
      inst.function = "RDTICK";
      break;
    case 5:  // rd %pc, rd
      inst.function = "RDPC";
      break;
    case 6:  // rd %fprs, rd
      inst.function = "RDFPRS";
      break;
    case 19:  // rd %gsr, rd
      inst.function = "RDGSR";
      break;
    case 22:  // rd %softint, rd
      inst.function = "RDSOFTINT";
      break;
    case 24:  // rd %stick, rd
      inst.function = "RDSTICK";
      break;
    case 25:  // rd %stick_cmpr, rd
      inst.function = "RDSICK_CMPR";
      break;
    case 26:  // rd %cfr, rd
      inst.function = "RDCFR";
      break;
    default: return false;
  }

  AddIntRegop(inst, enc.rd, kAddressSize, Operand::kActionWrite);
  return true;
}

static bool TryDecodeWRasr(Instruction &inst, uint32_t bits) {
  Format3ai0 enc_i0 = {bits};
  Format3ai1 enc_i1 = {bits};

  inst.category = Instruction::kCategoryNormal;
  switch (enc_i0.rd) {
    case 0:  // wr rs1, reg_or_imm, %y
      inst.function = "WRY";
      break;
    case 2:  // wr rs1, reg_or_imm, %ccr
      inst.function = "WRCCR";
      break;
    case 3:  //  wr rs1, reg_or_imm, %asi
      inst.function = "WRASI";
      break;
    case 6:  //  wr rs1, reg_or_imm, %fpsr
      inst.function = "WRFPRS";
      break;
    case 19:  //  wr rs1, reg_or_imm, %gsr
      inst.function = "WRGSR";
      break;
    case 20:  // wr rs1, reg_or_imm, %softint_set
      inst.function = "WRSOFTINT_SET";
      break;
    case 21:  // wr rs1, reg_or_imm, %softint_clr
      inst.function = "WRSOFTINT_CLR";
      break;
    case 22:  // wr rs1, reg_or_imm, %softint
      inst.function = "WRSOFTINT";
      break;
    case 25:  // wr rs1, reg_or_imm, %stick_cmpr
      inst.function = "WRSTICK_CMPR";
      break;
    case 27:  // wr rs1, reg_or_imm, %pause
      inst.function = "WRPAUSE";
      break;
    default: return false;
  }

  AddIntRegop(inst, enc_i0.rs1, kAddressSize, Operand::kActionRead);
  if (enc_i1.i) {
    AddImmop(inst, enc_i1.simm13, kAddressSize, true);
  } else {
    AddIntRegop(inst, enc_i0.rs2, kAddressSize, Operand::kActionRead);
  }
  return true;
}

static bool TryDecodeCALL(Instruction &inst, uint32_t bits) {
  union {
    uint32_t flat;
    struct {
      int32_t disp30 : 30;
      uint32_t op : 2;
    } __attribute__((packed));
  } __attribute__((packed)) enc;
  enc.flat = bits;

  inst.function = "CALL";
  int64_t disp = enc.disp30 << 2;
  if (inst.in_delay_slot) {
    inst.category = Instruction::kCategoryNormal;
    inst.has_branch_taken_delay_slot = false;
    inst.has_branch_not_taken_delay_slot = false;

  } else {
    inst.category = Instruction::kCategoryDirectFunctionCall;
    inst.delayed_pc = inst.next_pc;
    inst.has_branch_taken_delay_slot = true;
    inst.has_branch_not_taken_delay_slot = false;

    inst.branch_taken_pc =
        static_cast<uint32_t>(static_cast<int64_t>(inst.pc) + disp);

    inst.next_pc += 4;

    // NOTE(pag): This is `pc + 8`, which follows the convention that `ret`
    //            instructions (actually `jmpl`s) will return to the address
    //            of the `call` plus `8`.
    inst.branch_not_taken_pc = inst.next_pc;  // pc+8.
  }

  AddSrcRegop(inst, "PC", kAddressSize);  // Old PC.
  AddSrcRegop(inst, "NEXT_PC", kAddressSize);  // New PC.
  AddPCRelop(inst, disp);  // New NPC.
  AddIntRegop(inst, 15 /* %o7 */, kAddressSize, Operand::kActionWrite);
  AddPCDest(inst);
  AddNPCDest(inst);

  AddReturnPCDest(inst);  // Return address stored into `RETURN_PC`.

  if (inst.in_delay_slot) {
    inst.function = "UNSUPPORTED_DCTI";
    inst.operands.clear();
    inst.has_branch_taken_delay_slot = false;
    inst.has_branch_not_taken_delay_slot = false;
    inst.category = Instruction::kCategoryNormal;
    inst.next_pc = inst.pc + 4;
  }

  return true;
}


static bool TryDecodeJMPL(Instruction &inst, uint32_t bits) {
  Format3ai0 enc_i0 = {bits};
  Format3ai1 enc_i1 = {bits};

  AddSrcRegop(inst, "PC", kAddressSize);  // Old PC.
  AddSrcRegop(inst, "NEXT_PC", kAddressSize);  // New PC.

  inst.operands.emplace_back();
  auto &op = inst.operands.back();
  op.type = Operand::kTypeAddress;
  op.size = kAddressSize;
  op.action = Operand::kActionRead;
  op.addr.kind = Operand::Address::kControlFlowTarget;

  op.addr.address_size = kAddressSize;
  op.addr.base_reg.name = kReadIntRegName[enc_i1.rs1];
  op.addr.base_reg.size = kAddressSize;

  if (enc_i1.i) {
    op.addr.displacement = enc_i1.simm13;

  } else if (enc_i0.rs2) {
    op.addr.index_reg.name = kReadIntRegName[enc_i0.rs2];
    op.addr.index_reg.size = kAddressSize;
    op.addr.scale = 1;
  }

  if (!enc_i0.rd) {

    // NOTE(pag): This is stricter than what is in the manual, but is more in
    //            line with how we deal with function calls, and how actual
    //            software operates.
    //
    // NOTE(pag): The `8` byte displacement is common for functions returning
    //            values that can fit into registers. When RVO comes into play,
    //            an `unimp <struct size>` might be placed after the call's
    //            delay slot, which the callee must skip past in its return.
    if ((enc_i1.simm13 == 8 || enc_i1.simm13 == 12) &&
        (enc_i1.rs1 == 15 /* %o7 */ || enc_i1.rs1 == 31 /* %i7 */)) {
      inst.function = "RETL";
      inst.category = Instruction::kCategoryFunctionReturn;
    } else {
      inst.function = "JMPL";
      inst.category = Instruction::kCategoryIndirectJump;
    }

  } else if (enc_i0.rd == 15) {
    inst.function = "CALL_INDIRECT";
    inst.category = Instruction::kCategoryIndirectFunctionCall;

    // NOTE(pag): This is technically a lie; it is typical for functions to do
    //            `ret` which is a `jmpl %i7+8`.
    inst.branch_not_taken_pc = inst.pc + 8;

  } else {
    inst.function = "JMPL";
    inst.category = Instruction::kCategoryIndirectJump;
  }

  inst.has_branch_taken_delay_slot = true;
  inst.has_branch_not_taken_delay_slot = false;
  inst.delayed_pc = inst.next_pc;
  inst.next_pc += 4;

  AddIntRegop(inst, enc_i0.rd, kAddressSize, Operand::kActionWrite);
  AddPCDest(inst);
  AddNPCDest(inst);

  if (inst.IsFunctionCall()) {
    AddReturnPCDest(inst);
  }

  if (inst.in_delay_slot) {
    inst.function = "UNSUPPORTED_DCTI";
    inst.operands.clear();
    inst.has_branch_taken_delay_slot = false;
    inst.has_branch_not_taken_delay_slot = false;
    inst.category = Instruction::kCategoryNormal;
    inst.next_pc = inst.pc + 4;
  }

  return true;
}

static bool TryDecodeRETT(Instruction &inst, uint32_t bits) {
  Format3ai0 enc_i0 = {bits};
  Format3ai1 enc_i1 = {bits};
  inst.category = Instruction::kCategoryFunctionReturn;

  AddSrcRegop(inst, "NEXT_PC", kAddressSize);  // New PC.

  inst.operands.emplace_back();
  auto &dst_op = inst.operands.back();
  dst_op.type = Operand::kTypeAddress;
  dst_op.action = Operand::kActionRead;
  dst_op.size = kAddressSize;
  dst_op.addr.kind = Operand::Address::kControlFlowTarget;
  dst_op.addr.address_size = kAddressSize;

  if (enc_i1.i) {
    if (enc_i1.rs1) {
      if (enc_i1.simm13) {  // `r[rs1] + simm13`.
        dst_op.addr.base_reg.name = kReadIntRegName[enc_i1.rs1];
        dst_op.addr.base_reg.size = kAddressSize;
        dst_op.addr.displacement = enc_i1.simm13;

      } else {
        dst_op.type = Operand::kTypeRegister;
        dst_op.reg.name = kReadIntRegName[enc_i1.rs1];
        dst_op.reg.size = kAddressSize;
      }

    } else if (enc_i1.simm13) {  // `%g0 + simm13`.
      dst_op.type = Operand::kTypeImmediate;
      dst_op.imm.val = static_cast<int64_t>(enc_i1.simm13);

    } else {
      return false;  // RETT to `0`.
    }
  } else {
    if (enc_i0.rs1 && enc_i0.rs2) {  // `r[rs1] + r[rs2]`.
      dst_op.addr.base_reg.name = kReadIntRegName[enc_i0.rs1];
      dst_op.addr.base_reg.size = kAddressSize;

      dst_op.addr.index_reg.name = kReadIntRegName[enc_i0.rs2];
      dst_op.addr.index_reg.size = kAddressSize;
      dst_op.addr.scale = 1;

    } else if (enc_i0.rs1) {
      dst_op.type = Operand::kTypeRegister;
      dst_op.reg.name = kReadIntRegName[enc_i0.rs1];
      dst_op.reg.size = kAddressSize;

    } else if (enc_i0.rs2) {
      dst_op.type = Operand::kTypeRegister;
      dst_op.reg.name = kReadIntRegName[enc_i0.rs2];
      dst_op.reg.size = kAddressSize;

    } else {
      return false;  // RETT to `0`.
    }
  }

  AddPCDest(inst);
  AddNPCDest(inst);

  // Smuggle a stack-allocated register window into the semantics.
  AddDestRegop(inst, "PREV_WINDOW", kAddressSize);

  inst.function = "RETT";
  inst.has_branch_taken_delay_slot = true;
  inst.has_branch_not_taken_delay_slot = false;
  inst.delayed_pc = inst.next_pc;
  inst.next_pc += 4;

  // NOTE(pag): This is part of a SPARC idiom of `jmpl,rett`, but we don't
  //            have elaborate pipeline support to handle things. See
  //            semantics of `UNSUPPORTED_DCTI`.
  if (inst.in_delay_slot) {
    inst.function = "UNSUPPORTED_DCTI";
    inst.operands.clear();
    inst.has_branch_taken_delay_slot = false;
    inst.has_branch_not_taken_delay_slot = false;
    inst.category = Instruction::kCategoryNormal;
    inst.next_pc = inst.pc + 4;
  }

  return true;
}

static bool TryDecodeTcc(Instruction &inst, uint32_t bits) {
  union {
    uint32_t flat;
    struct {
      uint32_t rs2 : 5;
      uint32_t _0 : 8;
      uint32_t i : 1;
      uint32_t rs1 : 5;
      uint32_t op3 : 6;
      uint32_t cond : 4;
      uint32_t _1 : 1;
      uint32_t op : 2;
    } __attribute__((packed));
  } __attribute__((packed)) enc_i0 = {bits};
  static_assert(sizeof(enc_i0) == 4);

  union {
    uint32_t flat;
    struct {
      uint32_t imm7 : 7;
      uint32_t _0 : 6;
      uint32_t i : 1;
      uint32_t rs1 : 5;
      uint32_t op3 : 6;
      uint32_t cond : 4;
      uint32_t _1 : 1;
      uint32_t op : 2;
    } __attribute__((packed));
  } __attribute__((packed)) enc_i1 = {bits};
  static_assert(sizeof(enc_i1) == 4);

  inst.delayed_pc = 0;
  inst.has_branch_taken_delay_slot = false;
  inst.has_branch_not_taken_delay_slot = false;

  auto cond_name = kCondName[enc_i0.cond];

  inst.function.reserve(5);
  inst.function.push_back('T');
  inst.function += cond_name;

  // Trap always; handled by a *syncrhonous* hyper call. This way traps can
  // be raised inside of delay slots.
  if (enc_i1.cond == 0b1000) {
    if (inst.in_delay_slot) {
      inst.category = Instruction::kCategoryNormal;
      inst.function += "_sync";
    } else {
      inst.category = Instruction::kCategoryAsyncHyperCall;
      inst.branch_taken_pc = inst.next_pc;
    }

  // Trap never.
  } else if (enc_i1.cond == 0b0000) {
    if (inst.in_delay_slot) {
      inst.category = Instruction::kCategoryNoOp;
      inst.function += "_sync";

    } else {
      inst.category = Instruction::kCategoryDirectJump;
      inst.branch_taken_pc = inst.next_pc;
    }

  // Conditional trap.
  } else {

    // Conditional traps inside of a delay slot will turn into synchronous
    // hyper calls.
    if (inst.in_delay_slot) {
      inst.function += "_sync";
      inst.category = Instruction::kCategoryNormal;

    // Otherwise they induce their own control-flow.
    } else {
      inst.category = Instruction::kCategoryConditionalAsyncHyperCall;
      inst.branch_not_taken_pc = inst.next_pc;
    }
  }

  // TODO(pag): Handle write to TBR on `trap_instruction`.

  AddBranchTaken(inst);
  AddSrcRegop(inst, "NEXT_PC", 32);  // New PC on taken.
  AddNextPCRelop(inst, 4);  // New NPC on taken.

  // Trap vector number.
  if (enc_i1.i) {
    AddImmop(inst, enc_i1.imm7, 32, false);
  } else {
    AddIntRegop(inst, enc_i0.rs2, 32, Operand::kActionRead);
  }

  AddPCDest(inst);
  AddNPCDest(inst);

  return true;
}

// Generic decoder for conditional branches (Bcc, BPcc).
static bool TryDecode_Branch(Instruction &inst, unsigned cond, bool anul,
                             int64_t disp, std::string_view iform,
                             std::string_view ccr, bool is_fcc = false) {

  // Branch always.
  if (cond == 0b1000) {
    inst.category = Instruction::kCategoryDirectJump;
    inst.branch_taken_pc = inst.pc + disp;
    inst.has_branch_not_taken_delay_slot = false;

    if (!anul) {
      AddSrcRegop(inst, "NEXT_PC", kAddressSize);  // New PC.
      AddPCRelop(inst, disp);  // New NPC.

      inst.has_branch_taken_delay_slot = true;
      inst.delayed_pc = inst.next_pc;
      inst.next_pc += 4;

    } else {
      AddPCRelop(inst, disp);  // New PC.
      AddPCRelop(inst, disp + 4);  // New NPC.
      inst.has_branch_taken_delay_slot = false;
    }

  // Branch never.
  } else if (cond == 0b0000) {
    inst.category = Instruction::kCategoryDirectJump;

    if (!anul) {
      AddSrcRegop(inst, "NEXT_PC", kAddressSize);  // New PC.
      AddNextPCRelop(inst, 4);  // New NPC.

      inst.has_branch_taken_delay_slot = true;
      inst.has_branch_not_taken_delay_slot = false;
      inst.delayed_pc = inst.next_pc;

    } else {
      AddNextPCRelop(inst, 4);  // New PC.
      AddNextPCRelop(inst, 8);  // New NPC.

      inst.has_branch_taken_delay_slot = false;
      inst.has_branch_not_taken_delay_slot = false;
    }

    inst.next_pc += 4;
    inst.branch_taken_pc = inst.next_pc;

  // Conditional branch.
  } else {
    AddBranchTaken(inst);

    AddSrcRegop(inst, "NEXT_PC", kAddressSize);  // PC if taken.
    AddPCRelop(inst, disp);  // NPC if taken.

    inst.category = Instruction::kCategoryConditionalBranch;

    inst.branch_taken_pc = inst.pc + disp;
    inst.has_branch_taken_delay_slot = true;
    inst.delayed_pc = inst.next_pc;
    inst.next_pc += 4;
    inst.branch_not_taken_pc = inst.next_pc;  // Skip delayed instruction.

    // Not anulled means that the delayed instruction is executed on the taken
    // and not-taken paths.
    if (!anul) {
      AddSrcRegop(inst, "NEXT_PC", kAddressSize);  // PC if not taken.
      AddNextPCRelop(inst, 4);  // NPC if not taken.

      inst.has_branch_not_taken_delay_slot = true;

    // Anulled means that the delayed instruction is executed on the taken
    // path, but not on the not-taken path.
    } else {
      AddNextPCRelop(inst, 4);  // PC if not taken.
      AddNextPCRelop(inst, 8);  // NPC if not taken.

      inst.has_branch_not_taken_delay_slot = false;
    }
  }

  AddPCDest(inst);
  AddNPCDest(inst);

  // NOTE(pag): This is part of a SPARC idiom of `jmpl,rett`, but we don't
  //            have elaborate pipeline support to handle things. See
  //            semantics of `UNSUPPORTED_DCTI`.
  if (inst.in_delay_slot) {
    inst.function = "UNSUPPORTED_DCTI";
    inst.operands.clear();
    inst.has_branch_taken_delay_slot = false;
    inst.has_branch_not_taken_delay_slot = false;
    inst.category = Instruction::kCategoryNormal;
    inst.next_pc = inst.pc + 4;

  } else {
    inst.function.reserve(9);
    inst.function += iform;
    inst.function += (!is_fcc ? kCondName[cond] : kFCondName[cond]);
    inst.function.push_back('_');
    inst.function += ccr;  // `icc` or `xcc`.
  }

  return true;
}

static bool TryDecodeBcc(Instruction &inst, uint32_t bits) {
  Format0b enc = {bits};
  int64_t disp = enc.disp22 << 2;
  return TryDecode_Branch(inst, enc.cond, enc.a, disp, "B", "icc");
}

// SPARC v8+ instruction, found in v9 manual.
static bool TryDecodeBPcc(Instruction &inst, uint32_t bits) {
  Format0c enc = {bits};
  int64_t disp = enc.disp19 << 2;
  const auto cc = kCCRName[(enc.cc1 << 1u) | enc.cc0];
  if (cc.empty()) {
    return false;  // Reserved.
  }
  return TryDecode_Branch(inst, enc.cond, enc.a, disp, "B", cc);
}

// SPARC v8plus instruction, found in v9 manual.
static bool TryDecodeFBcc(Instruction &inst, uint32_t bits) {
  Format0b enc = {bits};
  int64_t disp = enc.disp22 << 2;
  return TryDecode_Branch(inst, enc.cond, enc.a, disp, "FB", "fcc0", true);
}

static bool TryDecodeFBPcc(Instruction &inst, uint32_t bits) {
  Format0c enc = {bits};
  int64_t disp = enc.disp19 << 2;
  const auto cc = kFCCRName[(enc.cc1 << 1u) | enc.cc0];
  if (cc.empty()) {
    return false;  // Reserved.
  }
  return TryDecode_Branch(inst, enc.cond, enc.a, disp, "FB", cc, true);
}

static bool TryDecodeBPr(Instruction &inst, uint32_t bits) {
  Format0d enc = {bits};
  if (enc.must_be_zero) {
    return false;
  }

  int64_t disp = static_cast<int16_t>((enc.d16hi << 14) | enc.d16lo);
  disp <<= 2;
  if (!enc.rcond || (enc.rcond == 0b100)) {
    return false;  // Reserved.
  }

  AddBranchTaken(inst);

  AddSrcRegop(inst, "NEXT_PC", kAddressSize);  // PC if taken.
  AddPCRelop(inst, disp);  // NPC if taken.

  inst.category = Instruction::kCategoryConditionalBranch;
  inst.branch_taken_pc = inst.pc + disp;
  inst.has_branch_taken_delay_slot = true;
  inst.delayed_pc = inst.next_pc;
  inst.next_pc += 4;
  inst.branch_not_taken_pc = inst.next_pc;  // Skip delayed instruction.

  // Not anulled means that the delayed instruction is executed on the taken
  // and not-taken paths.
  if (!enc.a) {
    AddSrcRegop(inst, "NEXT_PC", kAddressSize);  // PC if not taken.
    AddNextPCRelop(inst, 4);  // NPC if not taken.

    inst.has_branch_not_taken_delay_slot = true;

  // Anulled means that the delayed instruction is executed on the taken
  // path, but not on the not-taken path.
  } else {
    AddNextPCRelop(inst, 4);  // PC if not taken.
    AddNextPCRelop(inst, 8);  // NPC if not taken.

    inst.has_branch_not_taken_delay_slot = false;
  }

  AddPCDest(inst);
  AddNPCDest(inst);

  // NOTE(pag): This is part of a SPARC idiom of `jmpl,rett`, but we don't
  //            have elaborate pipeline support to handle things. See
  //            semantics of `UNSUPPORTED_DCTI`.
  if (inst.in_delay_slot) {
    inst.function = "UNSUPPORTED_DCTI";
    inst.operands.clear();
    inst.has_branch_taken_delay_slot = false;
    inst.has_branch_not_taken_delay_slot = false;
    inst.category = Instruction::kCategoryNormal;
    inst.next_pc = inst.pc + 4;

  } else {
    inst.function.reserve(9);
    inst.function.insert(0, "BR");
    inst.function += kRCondName[enc.rcond];
  }

  return true;
}

static bool TryDecodeCB(Instruction &inst, uint32_t bits) {
  Format0b enc = {bits};
  int64_t disp = enc.disp22 << 2;

  // Branch always.
  if (enc.cond == 0b1000) {
    inst.category = Instruction::kCategoryDirectJump;
    inst.branch_taken_pc = inst.pc + disp;
    inst.has_branch_not_taken_delay_slot = false;

    if (!enc.a) {
      AddSrcRegop(inst, "NEXT_PC", kAddressSize);  // New PC.
      AddPCRelop(inst, disp);  // New NPC.

      inst.has_branch_taken_delay_slot = true;
      inst.delayed_pc = inst.next_pc;
      inst.next_pc += 4;

    } else {
      AddPCRelop(inst, disp);  // New PC.
      AddPCRelop(inst, disp + 4);  // New NPC.
      inst.has_branch_taken_delay_slot = false;
    }

  // Branch never.
  } else if (enc.cond == 0b0000) {
    inst.category = Instruction::kCategoryDirectJump;

    if (!enc.a) {
      AddSrcRegop(inst, "NEXT_PC", kAddressSize);  // New PC.
      AddNextPCRelop(inst, 4);  // New NPC.

      inst.has_branch_taken_delay_slot = true;
      inst.has_branch_not_taken_delay_slot = false;
      inst.delayed_pc = inst.next_pc;

    } else {
      AddNextPCRelop(inst, 4);  // New PC.
      AddNextPCRelop(inst, 8);  // New NPC.

      inst.has_branch_taken_delay_slot = false;
      inst.has_branch_not_taken_delay_slot = false;
    }

    inst.next_pc += 4;
    inst.branch_taken_pc = inst.next_pc;

  // Conditional branch.
  } else {
    AddBranchTaken(inst);

    AddSrcRegop(inst, "NEXT_PC", kAddressSize);  // PC if taken.
    AddPCRelop(inst, disp);  // NPC if taken.

    inst.category = Instruction::kCategoryConditionalBranch;

    inst.branch_taken_pc = inst.pc + disp;
    inst.has_branch_taken_delay_slot = true;
    inst.delayed_pc = inst.next_pc;
    inst.next_pc += 4;
    inst.branch_not_taken_pc = inst.next_pc;  // Skip delayed instruction.

    // Not anulled means that the delayed instruction is executed on the taken
    // and not-taken paths.
    if (!enc.a) {
      AddSrcRegop(inst, "NEXT_PC", kAddressSize);  // PC if not taken.
      AddNextPCRelop(inst, 4);  // NPC if not taken.

      inst.has_branch_not_taken_delay_slot = true;

    // Anulled means that the delayed instruction is executed on the taken
    // path, but not on the not-taken path.
    } else {
      AddNextPCRelop(inst, 4);  // PC if not taken.
      AddNextPCRelop(inst, 8);  // NPC if not taken.

      inst.has_branch_not_taken_delay_slot = false;
    }
  }

  AddPCDest(inst);
  AddNPCDest(inst);

  // NOTE(pag): This is part of a SPARC idiom of `jmpl,rett`, but we don't
  //            have elaborate pipeline support to handle things. See
  //            semantics of `UNSUPPORTED_DCTI`.
  if (inst.in_delay_slot) {
    inst.function = "UNSUPPORTED_DCTI";
    inst.operands.clear();
    inst.has_branch_taken_delay_slot = false;
    inst.has_branch_not_taken_delay_slot = false;
    inst.category = Instruction::kCategoryNormal;
    inst.next_pc = inst.pc + 4;

  } else {
    inst.function.reserve(9);
    inst.function.insert(0, "CB");
    inst.function += kCondBrName[enc.cond];
  }

  return true;
}

static bool TryDecode_rs1_simm32_op_rs2_rd(Instruction &inst, uint32_t bits,
                                           const char *iform) {
  Format3ai0 enc_i0 = {bits};
  Format3ai1 enc_i1 = {bits};

  inst.function = iform;
  inst.category = Instruction::kCategoryNormal;
  AddIntRegop(inst, enc_i0.rs1, kAddressSize, Operand::kActionRead);

  if (enc_i1.i) {
    AddImmop(inst, enc_i1.simm13, kAddressSize, true);
  } else {
    AddIntRegop(inst, enc_i0.rs2, kAddressSize, Operand::kActionRead);
  }
  AddIntRegop(inst, enc_i0.rd, kAddressSize, Operand::kActionWrite);

  return true;
}

static bool TryDecode_rs1_imm_asi_op_rs2_rd(Instruction &inst, uint32_t bits,
                                            const char *iform) {
  Format3ai0 enc_i0 = {bits};

  inst.function = iform;
  inst.category = Instruction::kCategoryNormal;
  AddIntRegop(inst, enc_i0.rs1, kAddressSize, Operand::kActionRead);
  AddIntRegop(inst, enc_i0.rs2, kAddressSize, Operand::kActionRead);
  AddIntRegop(inst, enc_i0.rd, kAddressSize, Operand::kActionWrite);
  inst.function = iform;
  return true;
}

static bool TryDecodeSave(Instruction &inst, uint32_t bits) {
  if (!TryDecode_rs1_simm32_op_rs2_rd(inst, bits, "SAVE")) {
    return false;
  }

  // Smuggle a stack-allocated register window into the semantics.
  AddDestRegop(inst, "WINDOW", kAddressSize);
  AddDestRegop(inst, "PREV_WINDOW", kAddressSize);

  return true;
}

static bool TryDecodeRestore(Instruction &inst, uint32_t bits) {
  if (!TryDecode_rs1_simm32_op_rs2_rd(inst, bits, "RESTORE")) {
    return false;
  }

  // Smuggle a stack-allocated register window into the semantics.
  AddDestRegop(inst, "PREV_WINDOW", kAddressSize);

  return true;
}

static bool TryDecodeAND(Instruction &inst, uint32_t bits) {
  return TryDecode_rs1_simm32_op_rs2_rd(inst, bits, "AND");
}

static bool TryDecodeANDcc(Instruction &inst, uint32_t bits) {
  return TryDecode_rs1_simm32_op_rs2_rd(inst, bits, "ANDcc");
}

static bool TryDecodeANDN(Instruction &inst, uint32_t bits) {
  return TryDecode_rs1_simm32_op_rs2_rd(inst, bits, "ANDN");
}

static bool TryDecodeANDNcc(Instruction &inst, uint32_t bits) {
  return TryDecode_rs1_simm32_op_rs2_rd(inst, bits, "ANDNcc");
}

static bool TryDecodeOR(Instruction &inst, uint32_t bits) {
  return TryDecode_rs1_simm32_op_rs2_rd(inst, bits, "OR");
}

static bool TryDecodeORcc(Instruction &inst, uint32_t bits) {
  return TryDecode_rs1_simm32_op_rs2_rd(inst, bits, "ORcc");
}

static bool TryDecodeORN(Instruction &inst, uint32_t bits) {
  return TryDecode_rs1_simm32_op_rs2_rd(inst, bits, "ORN");
}

static bool TryDecodeORNcc(Instruction &inst, uint32_t bits) {
  return TryDecode_rs1_simm32_op_rs2_rd(inst, bits, "ORNcc");
}

static bool TryDecodeXOR(Instruction &inst, uint32_t bits) {
  return TryDecode_rs1_simm32_op_rs2_rd(inst, bits, "XOR");
}

static bool TryDecodeXORcc(Instruction &inst, uint32_t bits) {
  return TryDecode_rs1_simm32_op_rs2_rd(inst, bits, "XORcc");
}

static bool TryDecodeXNOR(Instruction &inst, uint32_t bits) {
  return TryDecode_rs1_simm32_op_rs2_rd(inst, bits, "XNOR");
}

static bool TryDecodeXNORcc(Instruction &inst, uint32_t bits) {
  return TryDecode_rs1_simm32_op_rs2_rd(inst, bits, "XNORcc");
}

static bool TryDecodeSUB(Instruction &inst, uint32_t bits) {
  return TryDecode_rs1_simm32_op_rs2_rd(inst, bits, "SUB");
}

static bool TryDecodeSUBcc(Instruction &inst, uint32_t bits) {
  return TryDecode_rs1_simm32_op_rs2_rd(inst, bits, "SUBcc");
}

static bool TryDecodeSUBX(Instruction &inst, uint32_t bits) {
  return TryDecode_rs1_simm32_op_rs2_rd(inst, bits, "SUBX");
}

static bool TryDecodeSUBXcc(Instruction &inst, uint32_t bits) {
  return TryDecode_rs1_simm32_op_rs2_rd(inst, bits, "SUBXcc");
}

static bool TryDecodeADD(Instruction &inst, uint32_t bits) {
  return TryDecode_rs1_simm32_op_rs2_rd(inst, bits, "ADD");
}

static bool TryDecodeADDcc(Instruction &inst, uint32_t bits) {
  return TryDecode_rs1_simm32_op_rs2_rd(inst, bits, "ADDcc");
}

static bool TryDecodeADDX(Instruction &inst, uint32_t bits) {
  return TryDecode_rs1_simm32_op_rs2_rd(inst, bits, "ADDX");
}

static bool TryDecodeADDXcc(Instruction &inst, uint32_t bits) {
  return TryDecode_rs1_simm32_op_rs2_rd(inst, bits, "ADDXcc");
}

static bool TryDecodeIMPDEP1(Instruction &inst, uint32_t bits) {
  Format3b enc = {bits};
  inst.function = "IMPDEP1";
  inst.category = Instruction::kCategoryNormal;
  AddImmop(inst, enc.opf, kAddressSize, false);
  return true;
}

struct fpu_opcode {
  std::string_view iform;
  uint32_t size;
};

#define SZERO 0
#define SWORD 32
#define DWORD 64
#define QWORD 128

static bool TryDecodeOpf_rs1_op_rs2_rd(Instruction &inst, uint32_t bits,
                                       uint32_t rs1_size, uint32_t rs2_size,
                                       uint32_t rd_size, const char *iform) {
  Format3b enc = {bits};
  inst.function = iform;
  inst.category = Instruction::kCategoryNormal;

  if (rs1_size && !AddFpuRegOp(inst, enc.rs1, rs1_size, Operand::kActionRead)) {
    return false;
  }

  if (rs2_size && !AddFpuRegOp(inst, enc.rs2, rs2_size, Operand::kActionRead)) {
    return false;
  }

  if (rd_size && !AddFpuRegOp(inst, enc.rd, rd_size, Operand::kActionWrite)) {
    return false;
  }
  return true;
}

#define DEFINE_FUNCTION(name, rs1_size, rs2_size, rd_size) \
  static bool TryDecode##name(Instruction &inst, uint32_t bits) { \
    return TryDecodeOpf_rs1_op_rs2_rd(inst, bits, rs1_size, rs2_size, rd_size, \
                                      #name); \
  }

DEFINE_FUNCTION(FABSS, SZERO, SWORD, SWORD)
DEFINE_FUNCTION(FABSD, SZERO, DWORD, DWORD)
DEFINE_FUNCTION(FABSQ, SZERO, QWORD, QWORD)
DEFINE_FUNCTION(FADDS, SWORD, SWORD, SWORD)
DEFINE_FUNCTION(FADDD, DWORD, DWORD, DWORD)
DEFINE_FUNCTION(FADDQ, QWORD, QWORD, QWORD)
DEFINE_FUNCTION(FSUBS, SWORD, SWORD, SWORD)
DEFINE_FUNCTION(FSUBD, DWORD, DWORD, DWORD)
DEFINE_FUNCTION(FSUBQ, QWORD, QWORD, QWORD)
DEFINE_FUNCTION(FDIVS, SWORD, SWORD, SWORD)
DEFINE_FUNCTION(FDIVD, DWORD, DWORD, DWORD)
DEFINE_FUNCTION(FDIVQ, QWORD, QWORD, QWORD)
DEFINE_FUNCTION(FHADDS, SWORD, SWORD, SWORD)
DEFINE_FUNCTION(FHADDD, DWORD, DWORD, DWORD)
DEFINE_FUNCTION(FMOVS, SZERO, SWORD, SWORD)
DEFINE_FUNCTION(FMOVD, SZERO, DWORD, DWORD)
DEFINE_FUNCTION(FMOVQ, SZERO, QWORD, QWORD)

DEFINE_FUNCTION(FMULS, SWORD, SWORD, SWORD)
DEFINE_FUNCTION(FMULD, DWORD, DWORD, DWORD)
DEFINE_FUNCTION(FMULQ, QWORD, QWORD, QWORD)
DEFINE_FUNCTION(FSMULD, SWORD, SWORD, DWORD)
DEFINE_FUNCTION(FDMULQ, DWORD, DWORD, QWORD)
DEFINE_FUNCTION(FXTOS, SZERO, DWORD, SWORD)
DEFINE_FUNCTION(FXTOD, SZERO, DWORD, DWORD)
DEFINE_FUNCTION(FXTOQ, SZERO, DWORD, QWORD)
DEFINE_FUNCTION(FITOS, SZERO, SWORD, SWORD)
DEFINE_FUNCTION(FITOD, SZERO, SWORD, DWORD)
DEFINE_FUNCTION(FITOQ, SZERO, SWORD, QWORD)
DEFINE_FUNCTION(FSTOX, SZERO, SWORD, DWORD)
DEFINE_FUNCTION(FDTOX, SZERO, DWORD, DWORD)
DEFINE_FUNCTION(FQTOX, SZERO, QWORD, DWORD)
DEFINE_FUNCTION(FSTOI, SZERO, SWORD, SWORD)
DEFINE_FUNCTION(FDTOI, SZERO, DWORD, SWORD)
DEFINE_FUNCTION(FQTOI, SZERO, QWORD, SWORD)

DEFINE_FUNCTION(FNEGS, SZERO, SWORD, SWORD)
DEFINE_FUNCTION(FNEGD, SZERO, DWORD, SWORD)
DEFINE_FUNCTION(FNEGQ, SZERO, QWORD, SWORD)

DEFINE_FUNCTION(FSQRTS, SZERO, SWORD, SWORD)
DEFINE_FUNCTION(FSQRTD, SZERO, DWORD, SWORD)
DEFINE_FUNCTION(FSQRTQ, SZERO, QWORD, SWORD)

DEFINE_FUNCTION(FSTOD, SZERO, SWORD, DWORD)
DEFINE_FUNCTION(FSTOQ, SZERO, SWORD, QWORD)
DEFINE_FUNCTION(FDTOS, SZERO, DWORD, SWORD)
DEFINE_FUNCTION(FDTOQ, SZERO, DWORD, QWORD)
DEFINE_FUNCTION(FQTOS, SZERO, QWORD, SWORD)
DEFINE_FUNCTION(FQTOD, SZERO, QWORD, DWORD)

#undef DEFINE_FUNCTION

static bool (*const kop10_op352Level[1u << 8])(Instruction &, uint32_t) = {
    [0b00000000] = nullptr,         [0b00000001] = TryDecodeFMOVS,
    [0b00000010] = TryDecodeFMOVD,  [0b00000011] = TryDecodeFMOVQ,
    [0b00000100] = nullptr,         [0b00000101] = TryDecodeFNEGS,
    [0b00000110] = TryDecodeFNEGD,  [0b00000111] = TryDecodeFNEGQ,
    [0b00001000] = nullptr,         [0b00001001] = TryDecodeFABSS,
    [0b00001010] = TryDecodeFABSD,  [0b00001011] = TryDecodeFABSQ,
    [0b00001100] = nullptr,         [0b00001101] = nullptr,
    [0b00001110] = nullptr,         [0b00001111] = nullptr,
    [0b00010000] = nullptr,         [0b00010001] = nullptr,
    [0b00010010] = nullptr,         [0b00010011] = nullptr,
    [0b00010100] = nullptr,         [0b00010101] = nullptr,
    [0b00010110] = nullptr,         [0b00010111] = nullptr,
    [0b00011000] = nullptr,         [0b00011001] = nullptr,
    [0b00011010] = nullptr,         [0b00011011] = nullptr,
    [0b00011100] = nullptr,         [0b00011101] = nullptr,
    [0b00011110] = nullptr,         [0b00011111] = nullptr,
    [0b00100000] = nullptr,         [0b00100001] = nullptr,
    [0b00100010] = nullptr,         [0b00100011] = nullptr,
    [0b00100100] = nullptr,         [0b00100101] = nullptr,
    [0b00100110] = nullptr,         [0b00100111] = nullptr,
    [0b00101000] = nullptr,         [0b00101001] = TryDecodeFSQRTS,
    [0b00101010] = TryDecodeFSQRTD, [0b00101011] = TryDecodeFSQRTQ,
    [0b00101100] = nullptr,         [0b00101101] = nullptr,
    [0b00101110] = nullptr,         [0b00101111] = nullptr,
    [0b00110000] = nullptr,         [0b00110001] = nullptr,
    [0b00110010] = nullptr,         [0b00110011] = nullptr,
    [0b00110100] = nullptr,         [0b00110101] = nullptr,
    [0b00110110] = nullptr,         [0b00110111] = nullptr,
    [0b00111000] = nullptr,         [0b00111001] = nullptr,
    [0b00111010] = nullptr,         [0b00111011] = nullptr,
    [0b00111100] = nullptr,         [0b00111101] = nullptr,
    [0b00111110] = nullptr,         [0b00111111] = nullptr,
    [0b01000000] = nullptr,         [0b01000001] = TryDecodeFADDS,
    [0b01000010] = TryDecodeFADDD,  [0b01000011] = TryDecodeFADDQ,
    [0b01000100] = nullptr,         [0b01000101] = TryDecodeFSUBS,
    [0b01000110] = TryDecodeFSUBD,  [0b01000111] = TryDecodeFSUBQ,
    [0b01001000] = nullptr,         [0b01001001] = TryDecodeFMULS,
    [0b01001010] = TryDecodeFMULD,  [0b01001011] = TryDecodeFMULQ,
    [0b01001100] = nullptr,         [0b01001101] = TryDecodeFDIVS,
    [0b01001110] = TryDecodeFDIVD,  [0b01001111] = TryDecodeFDIVQ,
    [0b01010000] = nullptr,         [0b01010001] = nullptr,
    [0b01010010] = nullptr,         [0b01010011] = nullptr,
    [0b01010100] = nullptr,         [0b01010101] = nullptr,
    [0b01010110] = nullptr,         [0b01010111] = nullptr,
    [0b01011000] = nullptr,         [0b01011001] = nullptr,
    [0b01011010] = nullptr,         [0b01011011] = nullptr,
    [0b01011100] = nullptr,         [0b01011101] = nullptr,
    [0b01011110] = nullptr,         [0b01011111] = nullptr,
    [0b01100000] = nullptr,         [0b01100001] = TryDecodeFHADDS,
    [0b01100010] = TryDecodeFHADDD, [0b01100011] = nullptr,
    [0b01100100] = nullptr,         [0b01100101] = nullptr,
    [0b01100110] = nullptr,         [0b01100111] = nullptr,
    [0b01101000] = nullptr,         [0b01101001] = TryDecodeFSMULD,
    [0b01101010] = nullptr,         [0b01101011] = nullptr,
    [0b01101100] = nullptr,         [0b01101101] = nullptr,
    [0b01101110] = TryDecodeFDMULQ, [0b01101111] = nullptr,
    [0b01110000] = nullptr,         [0b01110001] = nullptr,
    [0b01110010] = nullptr,         [0b01110011] = nullptr,
    [0b01110100] = nullptr,         [0b01110101] = nullptr,
    [0b01110110] = nullptr,         [0b01110111] = nullptr,
    [0b01111000] = nullptr,         [0b01111001] = nullptr,
    [0b01111010] = nullptr,         [0b01111011] = nullptr,
    [0b01111100] = nullptr,         [0b01111101] = nullptr,
    [0b01111110] = nullptr,         [0b01111111] = nullptr,
    [0b10000000] = nullptr,         [0b10000001] = TryDecodeFSTOX,
    [0b10000010] = TryDecodeFDTOX,  [0b10000011] = TryDecodeFQTOX,
    [0b10000100] = TryDecodeFXTOS,  [0b10000101] = nullptr,
    [0b10000110] = nullptr,         [0b10000111] = nullptr,
    [0b10001000] = TryDecodeFXTOD,  [0b10001001] = nullptr,
    [0b10001010] = nullptr,         [0b10001011] = nullptr,
    [0b10001100] = TryDecodeFXTOQ,  [0b10001101] = nullptr,
    [0b10001110] = nullptr,         [0b10001111] = nullptr,
    [0b10010000] = nullptr,         [0b10010001] = nullptr,
    [0b10010010] = nullptr,         [0b10010011] = nullptr,
    [0b10010100] = nullptr,         [0b10010101] = nullptr,
    [0b10010110] = nullptr,         [0b10010111] = nullptr,
    [0b10011000] = nullptr,         [0b10011001] = nullptr,
    [0b10011010] = nullptr,         [0b10011011] = nullptr,
    [0b10011100] = nullptr,         [0b10011101] = nullptr,
    [0b10011110] = nullptr,         [0b10011111] = nullptr,
    [0b10100000] = nullptr,         [0b10100001] = nullptr,
    [0b10100010] = nullptr,         [0b10100011] = nullptr,
    [0b10100100] = nullptr,         [0b10100101] = nullptr,
    [0b10100110] = nullptr,         [0b10100111] = nullptr,
    [0b10101000] = nullptr,         [0b10101001] = nullptr,
    [0b10101010] = nullptr,         [0b10101011] = nullptr,
    [0b10101100] = nullptr,         [0b10101101] = nullptr,
    [0b10101110] = nullptr,         [0b10101111] = nullptr,
    [0b10110000] = nullptr,         [0b10110001] = nullptr,
    [0b10110010] = nullptr,         [0b10110011] = nullptr,
    [0b10110100] = nullptr,         [0b10110101] = nullptr,
    [0b10110110] = nullptr,         [0b10110111] = nullptr,
    [0b10111000] = nullptr,         [0b10111001] = nullptr,
    [0b10111010] = nullptr,         [0b10111011] = nullptr,
    [0b10111100] = nullptr,         [0b10111101] = nullptr,
    [0b10111110] = nullptr,         [0b10111111] = nullptr,
    [0b11000000] = nullptr,         [0b11000001] = nullptr,
    [0b11000010] = nullptr,         [0b11000011] = nullptr,
    [0b11000100] = TryDecodeFITOS,  [0b11000101] = nullptr,
    [0b11000110] = TryDecodeFDTOS,  [0b11000111] = TryDecodeFQTOS,
    [0b11001000] = TryDecodeFITOD,  [0b11001001] = TryDecodeFSTOD,
    [0b11001010] = nullptr,         [0b11001011] = TryDecodeFQTOD,
    [0b11001100] = TryDecodeFITOQ,  [0b11001101] = TryDecodeFSTOQ,
    [0b11001110] = TryDecodeFDTOQ,  [0b11001111] = nullptr,
    [0b11010000] = nullptr,         [0b11010001] = TryDecodeFSTOI,
    [0b11010010] = TryDecodeFDTOI,  [0b11010011] = TryDecodeFQTOI,
    [0b11010100] = nullptr,         [0b11010101] = nullptr,
    [0b11010110] = nullptr,         [0b11010111] = nullptr,
    [0b11011000] = nullptr,         [0b11011001] = nullptr,
    [0b11011010] = nullptr,         [0b11011011] = nullptr,
    [0b11011100] = nullptr,         [0b11011101] = nullptr,
    [0b11011110] = nullptr,         [0b11011111] = nullptr,
    [0b11100000] = nullptr,         [0b11100001] = nullptr,
    [0b11100010] = nullptr,         [0b11100011] = nullptr,
    [0b11100100] = nullptr,         [0b11100101] = nullptr,
    [0b11100110] = nullptr,         [0b11100111] = nullptr,
    [0b11101000] = nullptr,         [0b11101001] = nullptr,
    [0b11101010] = nullptr,         [0b11101011] = nullptr,
    [0b11101100] = nullptr,         [0b11101101] = nullptr,
    [0b11101110] = nullptr,         [0b11101111] = nullptr,
    [0b11110000] = nullptr,         [0b11110001] = nullptr,
    [0b11110010] = nullptr,         [0b11110011] = nullptr,
    [0b11110100] = nullptr,         [0b11110101] = nullptr,
    [0b11110110] = nullptr,         [0b11110111] = nullptr,
    [0b11111000] = nullptr,         [0b11111001] = nullptr,
    [0b11111010] = nullptr,         [0b11111011] = nullptr,
    [0b11111100] = nullptr,         [0b11111101] = nullptr,
    [0b11111110] = nullptr,         [0b11111111] = nullptr,
};

static bool TryDecodeOpf52(Instruction &inst, uint32_t bits) {
  Format3b enc = {bits};
  auto func = kop10_op352Level[enc.opf];
  if (!func) {
    LOG(ERROR) << "OP=10 op3=110100 opf=" << std::bitset<8>(enc.opf);
    return TryDecodeIMPDEP1(inst, bits);
  }
  return func(inst, bits);
}

static bool TryDecodeFMOVcc(Instruction &inst, uint32_t bits) {
  union {
    uint32_t flat;
    struct {
      uint32_t rs2 : 5;
      uint32_t opf_low : 6;
      uint32_t opf_cc : 3;
      uint32_t cond : 4;
      uint32_t _1 : 1;
      uint32_t op3 : 6;
      uint32_t rd : 5;
      uint32_t op : 2;
    } __attribute__((packed));
  } __attribute__((packed)) enc = {bits};
  static_assert(sizeof(enc) == 4);

  const auto cc = kFCCRName[enc.opf_cc];
  if (cc.empty()) {
    return false;  // Reserved.
  }

  inst.category = Instruction::kCategoryNormal;
  inst.function.reserve(12);
  auto access_size = kAddressSize;
  switch (enc.opf_low) {
    case 0b0001:
      access_size = 32;
      inst.function.insert(0, "FMOVS");
      break;
    case 0b0010:
      access_size = 64;
      inst.function.insert(0, "FMOVD");
      break;
    case 0b0011:
      access_size = 128;
      inst.function.insert(0, "FMOVQ");
      break;
    default: return false;
  }

  AddFpuRegOp(inst, enc.rs2, access_size, Operand::kActionRead);
  AddFpuRegOp(inst, enc.rd, access_size, Operand::kActionWrite);

  inst.function +=
      (enc.opf_cc < 0b100) ? kFCondName[enc.cond] : kCondName[enc.cond];
  inst.function.push_back('_');
  inst.function += cc;
  return true;
}

static bool TryDecodeFMOVr(Instruction &inst, uint32_t bits) {
  union {
    uint32_t flat;
    struct {
      uint32_t rs2 : 5;
      uint32_t opf_low : 5;
      uint32_t rcond : 3;
      uint32_t _1 : 1;
      uint32_t rs1 : 5;
      uint32_t op3 : 6;
      uint32_t rd : 5;
      uint32_t op : 2;
    } __attribute__((packed));
  } __attribute__((packed)) enc = {bits};
  static_assert(sizeof(enc) == 4);

  if ((enc.rcond == 0b000) || (enc.rcond == 0b100)) {
    return false;  // Reserved.
  }

  inst.category = Instruction::kCategoryNormal;
  inst.function.reserve(9);
  auto access_size = kAddressSize;
  switch (enc.opf_low) {
    case 0b0001:
      access_size = 32;
      inst.function.insert(0, "FMOVRS");
      break;
    case 0b0010:
      access_size = 64;
      inst.function.insert(0, "FMOVRD");
      break;
    case 0b0011:
      access_size = 128;
      inst.function.insert(0, "FMOVRQ");
      break;
    default: return false;
  }

  AddIntRegop(inst, enc.rs1, kAddressSize, Operand::kActionRead);
  AddFpuRegOp(inst, enc.rs2, access_size, Operand::kActionRead);
  AddFpuRegOp(inst, enc.rd, access_size, Operand::kActionWrite);

  inst.function += kRCondName[enc.rcond];
  return true;
}

static bool TryDecodeFMOV(Instruction &inst, uint32_t bits) {
  union {
    uint32_t flat;
    struct {
      uint32_t rs2 : 5;
      uint32_t opf_low : 6;
      uint32_t opf_cc : 3;
      uint32_t cond : 4;
      uint32_t _1 : 1;
      uint32_t op3 : 6;
      uint32_t rd : 5;
      uint32_t op : 2;
    } __attribute__((packed));
  } __attribute__((packed)) enc = {bits};
  static_assert(sizeof(enc) == 4);

  if ((enc.opf_low == 0b0001) || (enc.opf_low == 0b0010) ||
      (enc.opf_low == 0b0011)) {
    return TryDecodeFMOVcc(inst, bits);
  }
  return TryDecodeFMOVr(inst, bits);
}

static const fpu_opcode Opf05[1 << 4U] = {
    [0b0000] = {{}, 0},
    [0b0001] = {"FCMPS", 0x00002020},
    [0b0010] = {"FCMPD", 0x00004040},
    [0b0011] = {"FCMPQ", 0x00008080},
    [0b0100] = {{}, 0},
    [0b0101] = {"FCMPES", 0x00002020},
    [0b0110] = {"FCMPED", 0x00004040},
    [0b0111] = {"FCMPEQ", 0x00008080},
    [0b1000] = {{}, 0},
    [0b1001] = {{}, 0},
    [0b1010] = {{}, 0},
    [0b1011] = {{}, 0},
    [0b1100] = {{}, 0},
    [0b1101] = {{}, 0},
    [0b1110] = {{}, 0},
    [0b1111] = {{}, 0},
};

static bool TryDecodeFCMP(Instruction &inst, uint32_t bits) {
  Format3c enc = {bits};
  union {
    uint32_t flat;
    struct {
      uint32_t rs1 : 8;
      uint32_t rs2 : 8;
      uint32_t rd : 8;
      uint32_t _1 : 8;
    } __attribute__((packed));
  } __attribute__((packed)) opd_size = {Opf05[enc.opf & 0b1111].size};

  const auto cc = kFCCRName[(enc.cc1 << 1u) | enc.cc0];
  if (cc.empty()) {
    return false;  // Reserved.
  }

  if (opd_size.rs1 &&
      !AddFpuRegOp(inst, enc.rs1, opd_size.rs1, Operand::kActionRead)) {
    return false;
  }

  if (opd_size.rs2 &&
      !AddFpuRegOp(inst, enc.rs2, opd_size.rs2, Operand::kActionRead)) {
    return false;
  }

  inst.category = Instruction::kCategoryNormal;
  inst.function.reserve(11);
  inst.function += Opf05[enc.opf & 0b1111].iform;
  inst.function.push_back('_');
  inst.function += cc;
  return true;
}

static bool TryDecodeFCMP_FMOV(Instruction &inst, uint32_t bits) {
  Format3c enc = {bits};
  auto shifted_opf = enc.opf >> 3;

  if (shifted_opf == 0b001010) {
    return TryDecodeFCMP(inst, bits);
  }

  return TryDecodeFMOV(inst, bits);
}


enum class RegClass { kInt, kFP };

static bool TryDecode_Load(Instruction &inst, uint32_t bits, const char *iform,
                           unsigned mem_size, unsigned reg_size,
                           RegClass rclass = RegClass::kInt) {
  Format3ai0 enc_i0 = {bits};
  Format3ai1 enc_i1 = {bits};
  inst.function = iform;
  inst.category = Instruction::kCategoryNormal;

  if (enc_i1.i) {
    AddBasePlusOffsetMemop(inst, Operand::kActionRead, mem_size, enc_i0.rs1, 0,
                           enc_i1.simm13);
  } else {
    AddBasePlusOffsetMemop(inst, Operand::kActionRead, mem_size, enc_i0.rs1,
                           enc_i0.rs2, 0);
  }

  if (RegClass::kInt == rclass) {
    AddIntRegop(inst, enc_i0.rd, reg_size, Operand::kActionWrite);

  } else if (!AddFpuRegOp(inst, enc_i0.rd, reg_size, Operand::kActionWrite)) {
    return false;
  }
  return true;
}

static bool TryDecode_Store(Instruction &inst, uint32_t bits, const char *iform,
                            unsigned reg_size, unsigned mem_size,
                            RegClass rclass = RegClass::kInt) {
  Format3ai0 enc_i0 = {bits};
  Format3ai1 enc_i1 = {bits};
  inst.function = iform;
  inst.category = Instruction::kCategoryNormal;

  if (RegClass::kInt == rclass) {
    AddIntRegop(inst, enc_i0.rd, reg_size, Operand::kActionRead);

  } else if (!AddFpuRegOp(inst, enc_i0.rd, reg_size, Operand::kActionRead)) {
    return false;
  }

  if (enc_i1.i) {
    AddBasePlusOffsetMemop(inst, Operand::kActionWrite, mem_size, enc_i0.rs1, 0,
                           enc_i1.simm13);
  } else {
    AddBasePlusOffsetMemop(inst, Operand::kActionWrite, mem_size, enc_i0.rs1,
                           enc_i0.rs2, 0);
  }
  return true;
}

static bool TryDecodeLDSB(Instruction &inst, uint32_t bits) {
  return TryDecode_Load(inst, bits, "LDSB", 8, kAddressSize);
}

static bool TryDecodeLDSH(Instruction &inst, uint32_t bits) {
  return TryDecode_Load(inst, bits, "LDSH", 16, kAddressSize);
}

static bool TryDecodeLDUB(Instruction &inst, uint32_t bits) {
  return TryDecode_Load(inst, bits, "LDUB", 8, kAddressSize);
}

static bool TryDecodeLDUH(Instruction &inst, uint32_t bits) {
  return TryDecode_Load(inst, bits, "LDUH", 16, kAddressSize);
}

static bool TryDecodeLD(Instruction &inst, uint32_t bits) {
  return TryDecode_Load(inst, bits, "LD", 32, 32);
}

static bool TryDecode_LoadDouble(Instruction &inst, uint32_t bits,
                                 const char *iform, unsigned access_size,
                                 RegClass rclass = RegClass::kInt) {
  Format3ai0 enc_i0 = {bits};
  Format3ai1 enc_i1 = {bits};
  inst.function = iform;
  inst.category = Instruction::kCategoryNormal;
  inst.is_atomic_read_modify_write = true;

  auto even_reg = enc_i0.rd;
  auto odd_reg = (enc_i0.rd + 1) & 0x1F;
  if (1 == (even_reg % 2)) {
    return false;  // Must be an even register.
  }
  if (enc_i1.i) {
    AddBasePlusOffsetMemop(inst, Operand::kActionRead, access_size, enc_i0.rs1,
                           0, enc_i1.simm13);
    AddBasePlusOffsetMemop(inst, Operand::kActionRead, access_size, enc_i0.rs1,
                           0, enc_i1.simm13 + (access_size / 8));
  } else {
    AddBasePlusOffsetMemop(inst, Operand::kActionRead, access_size, enc_i0.rs1,
                           enc_i0.rs2, 0);
    AddBasePlusOffsetMemop(inst, Operand::kActionRead, access_size, enc_i0.rs1,
                           enc_i0.rs2, access_size / 8);
  }

  if (RegClass::kInt == rclass) {
    AddIntRegop(inst, even_reg, kAddressSize, Operand::kActionWrite);
    AddIntRegop(inst, odd_reg, kAddressSize, Operand::kActionWrite);

  } else if (!AddFpuRegOp(inst, even_reg, access_size, Operand::kActionWrite) ||
             !AddFpuRegOp(inst, odd_reg, access_size, Operand::kActionWrite)) {
    return false;
  }

  return true;
}

static bool TryDecodeLDD(Instruction &inst, uint32_t bits) {
  return TryDecode_LoadDouble(inst, bits, "LDD", 32);
}

static bool TryDecodeLDF(Instruction &inst, uint32_t bits) {
  return TryDecode_Load(inst, bits, "LDF", 32, true);
}

static bool TryDecodeLDDF(Instruction &inst, uint32_t bits) {
  return TryDecode_LoadDouble(inst, bits, "LDDF", 32, RegClass::kInt);
}

static bool TryDecodeLDSTUB(Instruction &inst, uint32_t bits) {
  Format3ai0 enc_i0 = {bits};
  Format3ai1 enc_i1 = {bits};

  inst.function = "LDSTUB";
  inst.category = Instruction::kCategoryNormal;
  inst.is_atomic_read_modify_write = true;

  // if i != 0
  if (enc_i1.i) {
    AddBasePlusOffsetMemop(inst, Operand::kActionWrite, 8, enc_i0.rs1, 0,
                           enc_i1.simm13);
  } else {
    AddBasePlusOffsetMemop(inst, Operand::kActionWrite, 8, enc_i0.rs1, 0,
                           enc_i0.rs2);
  }

  AddIntRegop(inst, enc_i0.rd, kAddressSize, Operand::kActionWrite);
  return true;
}

static bool TryDecodeSTB(Instruction &inst, uint32_t bits) {
  return TryDecode_Store(inst, bits, "STB", kAddressSize, 8);
}

static bool TryDecodeSTH(Instruction &inst, uint32_t bits) {
  return TryDecode_Store(inst, bits, "STH", kAddressSize, 16);
}

static bool TryDecodeST(Instruction &inst, uint32_t bits) {
  return TryDecode_Store(inst, bits, "ST", 32, 32);
}

static bool TryDecode_StoreDouble(Instruction &inst, uint32_t bits,
                                  const char *iform, unsigned access_size,
                                  RegClass rclass = RegClass::kInt) {
  Format3ai0 enc_i0 = {bits};
  Format3ai1 enc_i1 = {bits};
  inst.function = iform;
  inst.category = Instruction::kCategoryNormal;
  inst.is_atomic_read_modify_write = true;

  auto even_reg = enc_i0.rd;
  auto odd_reg = (enc_i0.rd + 1) & 0x1F;
  if (1 == (even_reg % 2)) {
    return false;  // Must be an even register.
  }

  if (RegClass::kInt == rclass) {
    AddIntRegop(inst, even_reg, kAddressSize, Operand::kActionRead);
    AddIntRegop(inst, odd_reg, kAddressSize, Operand::kActionRead);

  } else if (!AddFpuRegOp(inst, even_reg, access_size, Operand::kActionRead) ||
             !AddFpuRegOp(inst, odd_reg, access_size, Operand::kActionRead)) {
    return false;
  }

  if (enc_i1.i) {
    AddBasePlusOffsetMemop(inst, Operand::kActionWrite, access_size, enc_i0.rs1,
                           0, enc_i1.simm13);
    AddBasePlusOffsetMemop(inst, Operand::kActionWrite, access_size, enc_i0.rs1,
                           0, enc_i1.simm13 + (access_size / 8));

  } else {
    AddBasePlusOffsetMemop(inst, Operand::kActionWrite, access_size, enc_i0.rs1,
                           enc_i0.rs2, 0);
    AddBasePlusOffsetMemop(inst, Operand::kActionWrite, access_size, enc_i0.rs1,
                           enc_i0.rs2, (access_size / 8));
  }
  return true;
}

static bool TryDecodeSTD(Instruction &inst, uint32_t bits) {
  return TryDecode_StoreDouble(inst, bits, "STD", 32);
}

static bool TryDecodeSTX(Instruction &inst, uint32_t bits) {
  return TryDecode_Store(inst, bits, "STX", 32, 32);
}

static bool TryDecodeSTF(Instruction &inst, uint32_t bits) {
  return TryDecode_Store(inst, bits, "STF", 32, 32, RegClass::kFP);
}

static bool TryDecodeSTDF(Instruction &inst, uint32_t bits) {
  return TryDecode_StoreDouble(inst, bits, "STDF", 32, RegClass::kFP);
}

static bool TryDecodeSETHI(Instruction &inst, uint32_t bits) {
  Format0a enc = {bits};
  if (enc.rd || enc.imm22) {
    inst.category = Instruction::kCategoryNormal;
    inst.function = "SETHI";
    AddImmop(inst, enc.imm22 << 10ull, kAddressSize, false);
    AddIntRegop(inst, enc.rd, kAddressSize, Operand::kActionWrite);

  } else {
    inst.category = Instruction::kCategoryNoOp;
    inst.function = "NOP";
  }

  return true;
}

static bool TryDecodeSET_IDIOM(Instruction &inst, uint32_t bits1,
                               uint32_t bits2, const char *base,
                               const char *multi) {
  Format0a enc1 = {bits1};
  Format3ai0 enc2_i0 = {bits2};
  Format3ai1 enc2_i1 = {bits2};

  const int32_t imm_high = enc1.imm22 << 10;

  if (enc2_i1.i) {
    const int32_t imm_low = enc2_i1.simm13;

    if (enc1.rd == enc2_i1.rd) {

      // This is the usual `SET` idiom:
      //    sethi imm_high, rd
      //    or rd, imm_low, rd
      if (enc2_i1.rs1 == enc1.rd) {

        //const auto imm = static_cast<uint32_t>(imm_low | imm_high);
        inst.function = "SET";
        AddImmop(inst, static_cast<uint32_t>(imm_high), kAddressSize, false);
        AddImmop(inst, static_cast<uint32_t>(imm_low), kAddressSize, false);
        AddIntRegop(inst, enc1.rd, kAddressSize, Operand::kActionWrite);

      // This is a possible variant, where the `sethi` is ultimately useless.
      //    sethi imm, rd
      //    or rs1, imm, rd
      } else {
        inst.function = base;
        AddIntRegop(inst, enc2_i1.rs1, kAddressSize, Operand::kActionRead);
        AddImmop(inst, imm_low, kAddressSize, false);
        AddIntRegop(inst, enc2_i1.rd, kAddressSize, Operand::kActionWrite);
      }

    // This is a variant of the `SET` idiom:
    //    sethi imm_high, rd1
    //    or rd1, imm_low, rd2
    //
    // This idiom can come up when multple XREFs share the same high bits and
    // can thus be built off of `rd1`.
    } else if (enc1.rd == enc2_i1.rs1) {
      inst.function = multi;
      AddImmop(inst, imm_high, kAddressSize, false);
      AddImmop(inst, imm_low, kAddressSize, false);
      AddIntRegop(inst, enc1.rd, kAddressSize, Operand::kActionWrite);
      AddIntRegop(inst, enc2_i1.rd, kAddressSize, Operand::kActionWrite);

    // This is not a SET idiom.
    } else {
      return false;
    }

  } else {
    if (enc1.rd == enc2_i0.rd) {

      // This is a variable `SET` idiom:
      //    sethi imm_high, rd
      //    or rd, rs2, rd
      if (enc2_i0.rs1 == enc1.rd) {
        inst.function = base;
        AddImmop(inst, imm_high, kAddressSize, false);
        AddIntRegop(inst, enc2_i0.rs2, kAddressSize, Operand::kActionRead);
        AddIntRegop(inst, enc1.rd, kAddressSize, Operand::kActionWrite);

      // Another variant of a vairable `SET` idiom:
      //    sethi imm_high, rd
      //    or rs1, rd, rd
      } else if (enc2_i0.rs2 == enc1.rd) {
        inst.function = base;
        AddIntRegop(inst, enc2_i0.rs1, kAddressSize, Operand::kActionRead);
        AddImmop(inst, imm_high, kAddressSize, false);
        AddIntRegop(inst, enc1.rd, kAddressSize, Operand::kActionWrite);

      // This is a possible variant, where the `sethi` is ultimately useless.
      //    sethi imm, rd
      //    or rs1, rs2, rd
      } else {
        inst.function = base;
        AddIntRegop(inst, enc2_i0.rs1, kAddressSize, Operand::kActionRead);
        AddIntRegop(inst, enc2_i0.rs2, kAddressSize, Operand::kActionRead);
        AddIntRegop(inst, enc1.rd, kAddressSize, Operand::kActionWrite);
      }

    // This is a variant of the `SET` idiom:
    //    sethi imm_high, rd1
    //    or rd1, rs2, rd2
    //
    // This idiom can come up when multple XREFs share the same high bits and
    // can thus be built off of `rd1`.
    } else if (enc1.rd == enc2_i0.rs1) {
      inst.function = multi;
      AddImmop(inst, imm_high, kAddressSize, false);
      AddIntRegop(inst, enc2_i0.rs2, kAddressSize, Operand::kActionRead);
      AddIntRegop(inst, enc1.rd, kAddressSize, Operand::kActionWrite);
      AddIntRegop(inst, enc2_i0.rd, kAddressSize, Operand::kActionWrite);

    // This is a variant of the `SET` idiom:
    //    sethi imm_high, rd1
    //    or rs1, rd1, rd2
    //
    // This idiom can come up when multple XREFs share the same high bits and
    // can thus be built off of `rd1`.
    } else if (enc1.rd == enc2_i0.rs2) {
      inst.function = multi;
      AddImmop(inst, imm_high, kAddressSize, false);
      AddIntRegop(inst, enc2_i0.rs1, kAddressSize, Operand::kActionRead);
      AddIntRegop(inst, enc1.rd, kAddressSize, Operand::kActionWrite);
      AddIntRegop(inst, enc2_i0.rd, kAddressSize, Operand::kActionWrite);

    // This is not a SET idiom.
    } else {
      return false;
    }
  }

  inst.category = Instruction::kCategoryNormal;
  return true;
}

static bool TryDecodeSET_SETHI_OR(Instruction &inst, uint32_t bits1,
                                  uint32_t bits2) {
  return TryDecodeSET_IDIOM(inst, bits1, bits2, "OR", "SETHI_OR");
}

static bool TryDecodeSET_SETHI_ADD(Instruction &inst, uint32_t bits1,
                                   uint32_t bits2) {
  return TryDecodeSET_IDIOM(inst, bits1, bits2, "ADD", "SETHI_ADD");
}

static bool TryDecodeUNIMP(Instruction &inst, uint32_t bits) {
  Format0a enc = {bits};
  if (inst.in_delay_slot) {
    inst.function = "UNIMP_SYNC";
    inst.category = Instruction::kCategoryNormal;
  } else {
    inst.function = "UNIMP_ASYNC";
    inst.category = Instruction::kCategoryError;
    inst.next_pc = 1;  // Never valid, as it's odd.
  }
  AddImmop(inst, enc.imm22, kAddressSize, false);
  return true;
}

static bool TryDecode_Shift(Instruction &inst, uint32_t bits,
                            const char *iform_name) {
  Format3ai0 enc_i0 = {bits};
  Format3ai0 enc_i1 = {bits};
  AddIntRegop(inst, enc_i0.rs1, kAddressSize, Operand::kActionRead);
  if (enc_i1.i) {
    /*    if (enc_i1.asi) {
      LOG(ERROR) << "TryDecode_Shift asi is null";
      return false;  // Reserved bits; must be zero.
    }*/
    AddImmop(inst, enc_i1.rs2 /* shcnt */, kAddressSize, false);

  // Embed the masking of the shift in the operand.
  } else if (enc_i0.rs2) {
    inst.operands.emplace_back();
    auto &op = inst.operands.back();
    op.type = Operand::kTypeShiftRegister;
    op.action = Operand::kActionRead;
    op.size = kAddressSize;
    op.shift_reg.reg.name = kReadIntRegName[enc_i0.rs2];
    op.shift_reg.reg.size = kAddressSize;
    op.shift_reg.shift_op = Operand::ShiftRegister::kShiftLeftWithZeroes;
    op.shift_reg.extend_op = Operand::ShiftRegister::kExtendUnsigned;
    op.shift_reg.shift_size = 0;
    op.shift_reg.extract_size = 5;

  // Register `%g0` is `rs2`.
  } else {
    AddImmop(inst, 0 /* shcnt */, kAddressSize, false);
  }

  AddIntRegop(inst, enc_i0.rd, kAddressSize, Operand::kActionWrite);
  inst.function = iform_name;
  inst.category = Instruction::kCategoryNormal;
  return true;
}

static bool TryDecodeSLL(Instruction &inst, uint32_t bits) {
  return TryDecode_Shift(inst, bits, "SLL");
}

static bool TryDecodeSRL(Instruction &inst, uint32_t bits) {
  return TryDecode_Shift(inst, bits, "SRL");
}

static bool TryDecodeSRA(Instruction &inst, uint32_t bits) {
  return TryDecode_Shift(inst, bits, "SRA");
}

static bool TryDecodeMOVcc(Instruction &inst, uint32_t bits) {
  Format4c enc_i0 = {bits};
  Format4d enc_i1 = {bits};
  auto cc_index = (enc_i0.cc2 << 2u) | (enc_i0.cc1 << 1u) | enc_i0.cc0;
  const auto cc = kFCCRName[cc_index];
  if (cc.empty()) {
    return false;  // Reserved.
  }

  if (enc_i1.i) {
    AddImmop(inst, static_cast<int64_t>(enc_i1.simm11), kAddressSize, true);
  } else {
    AddIntRegop(inst, enc_i0.rs2, kAddressSize, Operand::kActionRead);
  }

  AddIntRegop(inst, enc_i0.rd, kAddressSize, Operand::kActionWrite);

  inst.category = Instruction::kCategoryNormal;
  inst.function.reserve(12);
  inst.function.insert(0, "MOV");
  inst.function +=
      (cc_index < 0b100) ? kFCondName[enc_i0.cond] : kCondName[enc_i0.cond];
  inst.function.push_back('_');
  inst.function += cc;
  return true;
}

static bool TryDecodeMOVr(Instruction &inst, uint32_t bits) {
  Format3di0 enc_i0 = {bits};
  Format3di1 enc_i1 = {bits};

  const auto cc = kRCondName[enc_i0.rcond];
  if (cc.empty()) {
    return false;  // Reserved.
  }

  if (enc_i1.i) {
    AddIntRegop(inst, enc_i1.rs1, kAddressSize, Operand::kActionRead);
    AddImmop(inst, static_cast<int64_t>(enc_i1.simm10), kAddressSize, true);
  } else {
    AddIntRegop(inst, enc_i0.rs1, kAddressSize, Operand::kActionRead);
    AddIntRegop(inst, enc_i0.rs2, kAddressSize, Operand::kActionRead);
  }

  AddIntRegop(inst, enc_i0.rd, kAddressSize, Operand::kActionWrite);

  inst.category = Instruction::kCategoryNormal;
  inst.function.reserve(12);
  inst.function.insert(0, "MOVR");
  inst.function += cc;
  return true;
}

static bool TryDecodeUMUL(Instruction &inst, uint32_t bits) {
  return TryDecode_rs1_simm32_op_rs2_rd(inst, bits, "UMUL");
}

static bool TryDecodeSMUL(Instruction &inst, uint32_t bits) {
  return TryDecode_rs1_simm32_op_rs2_rd(inst, bits, "SMUL");
}

static bool TryDecodeUMULcc(Instruction &inst, uint32_t bits) {
  return TryDecode_rs1_simm32_op_rs2_rd(inst, bits, "UMULcc");
}

static bool TryDecodeSMULcc(Instruction &inst, uint32_t bits) {
  return TryDecode_rs1_simm32_op_rs2_rd(inst, bits, "SMULcc");
}

static bool TryDecodeUDIV(Instruction &inst, uint32_t bits) {
  return TryDecode_rs1_simm32_op_rs2_rd(inst, bits, "UDIV");
}

static bool TryDecodeSDIV(Instruction &inst, uint32_t bits) {
  return TryDecode_rs1_simm32_op_rs2_rd(inst, bits, "SDIV");
}

static bool TryDecodeUDIVcc(Instruction &inst, uint32_t bits) {
  return TryDecode_rs1_simm32_op_rs2_rd(inst, bits, "UDIVcc");
}

static bool TryDecodeSDIVcc(Instruction &inst, uint32_t bits) {
  return TryDecode_rs1_simm32_op_rs2_rd(inst, bits, "SDIVcc");
}

static bool TryDecodeMULX(Instruction &inst, uint32_t bits) {
  return TryDecode_rs1_simm32_op_rs2_rd(inst, bits, "MULX");
}

static bool TryDecodeMULScc(Instruction &inst, uint32_t bits) {
  return TryDecode_rs1_simm32_op_rs2_rd(inst, bits, "MULScc");
}

static bool TryDecodeCASA(Instruction &inst, uint32_t bits) {
  inst.is_atomic_read_modify_write = true;
  return TryDecode_rs1_imm_asi_op_rs2_rd(inst, bits, "CASA");
}

static bool TryDecodeSWAP(Instruction &inst, uint32_t bits) {
  Format3ai0 enc_i0 = {bits};
  Format3ai1 enc_i1 = {bits};

  inst.is_atomic_read_modify_write = true;
  inst.function = "SWAP";
  inst.category = Instruction::kCategoryNormal;

  // if i != 0
  if (enc_i1.i) {
    AddBasePlusOffsetMemop(inst, Operand::kActionWrite, kAddressSize,
                           enc_i0.rs1, 0, enc_i1.simm13);
  } else {
    AddBasePlusOffsetMemop(inst, Operand::kActionWrite, kAddressSize,
                           enc_i0.rs1, 0, enc_i0.rs2);
  }

  AddIntRegop(inst, enc_i0.rd, kAddressSize, Operand::kActionWrite);
  return true;
}


static bool (*const kop00_op2Level[1u << 3])(Instruction &, uint32_t) = {
    [0b000] = TryDecodeUNIMP, [0b001] = TryDecodeBPcc,
    [0b010] = TryDecodeBcc,   [0b011] = TryDecodeBPr,
    [0b100] = TryDecodeSETHI, [0b101] = TryDecodeFBPcc,
    [0b110] = TryDecodeFBcc,  [0b111] = TryDecodeCB,
};

static bool (*const kop10_op3Level[1U << 6])(Instruction &, uint32_t) = {
    [0b000000] = TryDecodeADD,    [0b000001] = TryDecodeAND,
    [0b000010] = TryDecodeOR,     [0b000011] = TryDecodeXOR,
    [0b000100] = TryDecodeSUB,    [0b000101] = TryDecodeANDN,
    [0b000110] = TryDecodeORN,    [0b000111] = TryDecodeXNOR,
    [0b001000] = TryDecodeADDX,   [0b001001] = TryDecodeMULX,
    [0b001010] = TryDecodeUMUL,   [0b001011] = TryDecodeSMUL,
    [0b001100] = TryDecodeSUBX,   [0b001101] = nullptr,
    [0b001110] = TryDecodeUDIV,   [0b001111] = TryDecodeSDIV,
    [0b010000] = TryDecodeADDcc,  [0b010001] = TryDecodeANDcc,
    [0b010010] = TryDecodeORcc,   [0b010011] = TryDecodeXORcc,
    [0b010100] = TryDecodeSUBcc,  [0b010101] = TryDecodeANDNcc,
    [0b010110] = TryDecodeORNcc,  [0b010111] = TryDecodeXNORcc,
    [0b011000] = TryDecodeADDXcc, [0b011001] = nullptr,
    [0b011010] = TryDecodeUMULcc, [0b011011] = TryDecodeSMULcc,
    [0b011100] = TryDecodeSUBXcc, [0b011101] = nullptr,
    [0b011110] = TryDecodeUDIVcc, [0b011111] = TryDecodeSDIVcc,
    [0b100000] = nullptr,         [0b100001] = nullptr,
    [0b100010] = nullptr,         [0b100011] = nullptr,
    [0b100100] = TryDecodeMULScc, [0b100101] = TryDecodeSLL,
    [0b100110] = TryDecodeSRL,    [0b100111] = TryDecodeSRA,
    [0b101000] = TryDecodeRDasr,  [0b101001] = nullptr,
    [0b101010] = nullptr,         [0b101011] = nullptr,
    [0b101100] = TryDecodeMOVcc,  [0b101101] = nullptr,
    [0b101110] = nullptr,         [0b101111] = TryDecodeMOVr,
    [0b110000] = TryDecodeWRasr,  [0b110001] = nullptr,
    [0b110010] = nullptr,         [0b110011] = nullptr,
    [0b110100] = TryDecodeOpf52,  [0b110101] = TryDecodeFCMP_FMOV,
    [0b110110] = nullptr,         [0b110111] = nullptr,
    [0b111000] = TryDecodeJMPL,   [0b111001] = TryDecodeRETT,
    [0b111010] = TryDecodeTcc,    [0b111011] = nullptr,
    [0b111100] = TryDecodeSave,   [0b111101] = TryDecodeRestore,
    [0b111110] = nullptr,         [0b111111] = nullptr,
};

static bool (*const kop11_op3Level[1u << 6])(Instruction &, uint32_t) = {
    [0b000000] = TryDecodeLD,   [0b000001] = TryDecodeLDUB,
    [0b000010] = TryDecodeLDUH, [0b000011] = TryDecodeLDD,
    [0b000100] = TryDecodeST,   [0b000101] = TryDecodeSTB,
    [0b000110] = TryDecodeSTH,  [0b000111] = TryDecodeSTD,
    [0b001000] = nullptr,       [0b001001] = TryDecodeLDSB,
    [0b001010] = TryDecodeLDSH, [0b001011] = nullptr,
    [0b001100] = nullptr,       [0b001101] = TryDecodeLDSTUB,
    [0b001110] = TryDecodeSTX,  [0b001111] = TryDecodeSWAP,
    [0b010000] = nullptr,       [0b010001] = nullptr,
    [0b010010] = nullptr,       [0b010011] = nullptr,
    [0b010100] = nullptr,       [0b010101] = nullptr,
    [0b010110] = nullptr,       [0b010111] = nullptr,
    [0b011000] = nullptr,       [0b011001] = nullptr,
    [0b011010] = nullptr,       [0b011011] = nullptr,
    [0b011100] = nullptr,       [0b011101] = nullptr,
    [0b011110] = nullptr,       [0b011111] = nullptr,
    [0b100000] = TryDecodeLDF,  [0b100001] = nullptr,
    [0b100010] = nullptr,       [0b100011] = TryDecodeLDDF,
    [0b100100] = TryDecodeSTF,  [0b100101] = nullptr,
    [0b100110] = nullptr,       [0b100111] = TryDecodeSTDF,
    [0b101000] = nullptr,       [0b101001] = nullptr,
    [0b101010] = nullptr,       [0b101011] = nullptr,
    [0b101100] = nullptr,       [0b101101] = nullptr,
    [0b101110] = nullptr,       [0b101111] = nullptr,
    [0b110000] = nullptr,       [0b110001] = nullptr,
    [0b110010] = nullptr,       [0b110011] = nullptr,
    [0b110100] = nullptr,       [0b110101] = nullptr,
    [0b110110] = nullptr,       [0b110111] = nullptr,
    [0b111000] = nullptr,       [0b111001] = nullptr,
    [0b111010] = nullptr,       [0b111011] = nullptr,
    [0b111100] = TryDecodeCASA, [0b111101] = nullptr,
    [0b111110] = nullptr,       [0b111111] = nullptr,

    //[0b100001] = TryDecodeLDFSR
    //[0b100101] = TryDecodeSTFSR,
    //[0b100110] = TryDecodeSTDFQ,
    // [0b111110] = TryDecodeCASXA,
};

// SETHI, Branches, and ILLTRAP
static bool TryDecode_op00(Instruction &inst, uint32_t bits) {
  auto index = (bits >> 22u) & 0x7u;
  auto func = kop00_op2Level[index];
  if (!func) {
    LOG(ERROR) << "OP=00 op2=" << std::bitset<3>(index);
    return false;
  }
  return func(inst, bits);
}

// It's a PC-relative CALL instruction.
static bool TryDecode_op01(Instruction &inst, uint32_t bits) {
  return TryDecodeCALL(inst, bits);
}

static bool TryDecode_op10(Instruction &inst, uint32_t bits) {
  auto index = (bits >> 19u) & 0x3Fu;
  auto func = kop10_op3Level[index];
  if (!func) {
    LOG(ERROR) << "OP=10 op3=" << std::bitset<6>(index);
    return false;
  }
  return func(inst, bits);
}

static bool TryDecode_op11(Instruction &inst, uint32_t bits) {
  auto index = (bits >> 19u) & 0x3Fu;
  auto func = kop11_op3Level[index];
  if (!func) {
    LOG(ERROR) << "OP=11 op3=" << std::bitset<6>(index);
    return false;
  }
  return func(inst, bits);
}

static bool (*const kopLevel[])(Instruction &, uint32_t) = {
    TryDecode_op00, TryDecode_op01, TryDecode_op10, TryDecode_op11};

static uint32_t BytesToBits(const uint8_t *bytes) {
  uint32_t bits = 0;
  bits = (bits << 8) | static_cast<uint32_t>(bytes[0]);
  bits = (bits << 8) | static_cast<uint32_t>(bytes[1]);
  bits = (bits << 8) | static_cast<uint32_t>(bytes[2]);
  bits = (bits << 8) | static_cast<uint32_t>(bytes[3]);
  return bits;
}

}  // namespace

bool TryDecode(Instruction &inst) {
  const auto num_bytes = inst.bytes.size();
  if (num_bytes == 4) {
    const auto bytes = reinterpret_cast<const uint8_t *>(inst.bytes.data());
    const auto bits = BytesToBits(bytes);
    return kopLevel[bits >> 30u](inst, bits);

  // Pseudo-operations, e.g. SET=SETHI+OR.
  } else if (num_bytes == 8) {

    if (inst.in_delay_slot) {
      LOG(WARNING) << "Decoding 8-byte pseudo-op at " << std::hex << inst.pc
                   << std::dec << " in delay slot; ignoring second four bytes";
      inst.bytes.resize(4);
      inst.next_pc = inst.pc + 4;
      return TryDecode(inst);
    }

    const auto bytes = reinterpret_cast<const uint8_t *>(inst.bytes.data());
    const auto bits1 = BytesToBits(bytes);
    const auto bits2 = BytesToBits(&(bytes[4]));

    // op=00, op2=0b100
    const auto bits1_op = bits1 >> 30u;
    const auto bits1_op2 = (bits1 >> 22u) & 0x7u;
    bool ret = false;
    if (bits1_op == 0b00 && bits1_op2 == 0b100) {  // SETHI.
      const auto bits2_op = bits2 >> 30u;
      const auto bits2_op3 = (bits2 >> 19u) & 0x3Fu;
      if (bits2_op == 0b10 && bits2_op3 == 0b000010) {  // OR.
        ret = TryDecodeSET_SETHI_OR(inst, bits1, bits2);
      } else if (bits2_op == 0b10 && bits2_op3 == 0b000000) {  // ADD
        ret = TryDecodeSET_SETHI_ADD(inst, bits1, bits2);
      }
    }

    if (!ret) {
      inst.bytes.resize(4);
      inst.next_pc = inst.pc + 4;
      ret = TryDecode(inst);

      LOG_IF(ERROR, !ret) << "Unsupported 8-byte instruction: "
                          << inst.Serialize();
    }
    return ret;

  } else {
    return false;
  }
}

}  // namespace sparc32
}  // namespace remill
