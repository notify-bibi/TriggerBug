/*
 * Copyright (c) 2017 Trail of Bits, Inc.
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

#include "remill/Arch/Name.h"

#include <llvm/ADT/Triple.h>

namespace remill {

ArchName GetArchName(const llvm::Triple &triple) {
  switch (triple.getArch()) {
    case llvm::Triple::ArchType::x86: return kArchX86;
    case llvm::Triple::ArchType::x86_64: return kArchAMD64;
    case llvm::Triple::ArchType::aarch64: return kArchAArch64LittleEndian;
    case llvm::Triple::ArchType::arm: return kArchAArch32LittleEndian;
    case llvm::Triple::ArchType::thumb: return kArchAArch32LittleEndian;
    default: return kArchInvalid;
  }
}

ArchName GetArchName(std::string_view arch_name) {
  if (arch_name == "x86") {
    return kArchX86;

  } else if (arch_name == "x86_avx") {
    return kArchX86_AVX;

  } else if (arch_name == "x86_avx512") {
    return kArchX86_AVX512;

  } else if (arch_name == "amd64") {
    return kArchAMD64;

  } else if (arch_name == "amd64_avx") {
    return kArchAMD64_AVX;

  } else if (arch_name == "amd64_avx512") {
    return kArchAMD64_AVX512;

  } else if (arch_name == "aarch32") {
    return kArchAArch32LittleEndian;

  } else if (arch_name == "aarch64") {
    return kArchAArch64LittleEndian;

  } else if (arch_name == "sparc32") {
    return kArchSparc32;

  } else if (arch_name == "sparc64") {
    return kArchSparc64;

  } else {
    return kArchInvalid;
  }
}

namespace {

static const std::string_view kArchNames[] = {
    [kArchInvalid] = "invalid",
    [kArchX86] = "x86",
    [kArchX86_AVX] = "x86_avx",
    [kArchX86_AVX512] = "x86_avx512",
    [kArchAMD64] = "amd64",
    [kArchAMD64_AVX] = "amd64_avx",
    [kArchAMD64_AVX512] = "amd64_avx512",
    [kArchAArch32LittleEndian] = "aarch32",
    [kArchAArch64LittleEndian] = "aarch64",
    [kArchSparc32] = "sparc32",
    [kArchSparc64] = "sparc64",
};

}  // namespace

std::string_view GetArchName(ArchName arch_name) {
  return kArchNames[arch_name];
}

}  // namespace remill
