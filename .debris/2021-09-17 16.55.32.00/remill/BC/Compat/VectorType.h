/*
 * Copyright (c) 2020 Trail of Bits, Inc.
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

#pragma once

#include <llvm/IR/Instructions.h>

#include "remill/BC/Version.h"

// Hack in a 'FixedVectorType' for LLVM < 11
namespace llvm {
#if LLVM_VERSION_NUMBER < LLVM_VERSION(11, 0)
using FixedVectorType = VectorType;
#endif


inline static constexpr auto GetFixedVectorTypeId(void) {
#if LLVM_VERSION_NUMBER < LLVM_VERSION(11, 0)
  return Type::VectorTyID;
#else
  return Type::FixedVectorTyID;
#endif
}

}  // namespace llvm
