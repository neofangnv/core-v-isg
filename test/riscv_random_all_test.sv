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

`ifndef RISCV_RANDOM_ALL_TEST__SV
`define RISCV_RANDOM_ALL_TEST__SV

class riscv_random_all_test extends riscv_test_base;
    `uvm_component_utils(riscv_random_all_test)

    riscv_random_all_seq seq0;

    function new(string name, uvm_component parent = null);
        super.new(name, parent);
    endfunction

    function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        seq0 = riscv_random_all_seq::type_id::create("random all seq",,get_full_name());
    endfunction: build_phase

    task main_phase(uvm_phase phase);
        super.main_phase(phase);
        seq0.randomize();
        seq0.start(null);
        dump_mem_to_file();
    endtask: main_phase
endclass: riscv_random_all_test

`endif // RISCV_RANDOM_ALL_TEST__SV
