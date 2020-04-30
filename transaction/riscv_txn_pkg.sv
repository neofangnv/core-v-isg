//
// Copyright (c) 2017, NVIDIA CORPORATION.  All rights reserved.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.
//

`ifndef RISCV_TXN_PKG__SV
`define RISCV_TXN_PKG__SV

`include "uvm_macros.svh"

package riscv_txn_pkg;
	import uvm_pkg::*;

	`include "riscv_inst_base_txn.sv"
endpackage: riscv_txn_pkg

`endif // RISCV_TXN_PKG__SV
