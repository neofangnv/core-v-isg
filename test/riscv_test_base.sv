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

`ifndef RISCV_TEST_BASE__SV
`define RISCV_TEST_BASE__SV

class riscv_test_base extends uvm_test;
    `uvm_component_utils(riscv_test_base)

    riscv_mem mem;

    /////////////////////////////////////////////////////////////////////////
    /// new()
    /////////////////////////////////////////////////////////////////////////
    function new(string name, uvm_component parent=null);
        super.new(name, parent);
    endfunction : new
    
    /////////////////////////////////////////////////////////////////////////
    /// build_phase
    /////////////////////////////////////////////////////////////////////////
    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        mem = riscv_mem::type_id::create("mem", this);
    endfunction : build_phase

    /////////////////////////////////////////////////////////////////////////
    /// main_phase
    /////////////////////////////////////////////////////////////////////////
    virtual task main_phase(uvm_phase phase);
        super.main_phase(phase);
    endtask

    virtual task dump_mem_to_file();
        mem.mem_storeh("dump_mem.txt");
    endtask
endclass: riscv_test_base

`endif // RISCV_TEST_BASE__SV
