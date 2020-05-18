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

`ifndef RISCV_RANDOM_ALL_SEQ__SV
`define RISCV_RANDOM_ALL_SEQ__SV

// This is an example to show how to use random generator
// gen_inst() function should be overrided to implement corresponding constraint
// gen_valid_sequence() is the main function to generate a valid sequence
class riscv_random_all_seq extends riscv_base_seq;

    `uvm_object_utils(riscv_random_all_seq)

    riscv_inst_base_txn tr;

    bit enable_branch;
	bit enable_backward_branch;
	bit enable_load_store;
	bit enable_csr;

    int insert_csr_freq;
	int branch_weight;
	int load_store_weight;

    function new (string name = "riscv_random_all_seq");
        super.new(name);

        if (!$value$plusargs("BRANCH_EN=%d", enable_branch)) begin
            enable_branch = 0;
        end
        if (!$value$plusargs("BACKWARD_BRANCH_EN=%d", enable_backward_branch)) begin
            enable_backward_branch = 0;
        end
        if (!$value$plusargs("LOAD_STORE_EN=%d", enable_load_store)) begin
            enable_load_store = 0;
        end
        if (!$value$plusargs("CSR_EN=%d", enable_csr)) begin
            enable_csr = 0;
        end
        if (!$value$plusargs("CSR_FREQ=%d", insert_csr_freq)) begin
            insert_csr_freq = 500;
        end
    endfunction: new
    
    // NEED_CHANGE, setup constraint as you want
	virtual function riscv_inst_base_txn gen_inst(bit[63:0] pc, bit gen_inst_32_en, ref bit gen_fail);
        bit [255:0] pa;
        bit result;
		bit only_forward_jump;

        tr = riscv_inst_base_txn::type_id::create("tr",,get_full_name());

		branch_weight = enable_branch ? 1 : 0;
		load_store_weight = enable_load_store ? 1 : 0;

        void'(tr.randomize() with {
            inst_type dist {[OP_LUI:OP_SRAW]:/10, [OP_BEQ:OP_BGEU]:/branch_weight, [OP_MUL:OP_REMUW]:/10, [OP_LB:OP_SD]:/load_store_weight};

			rs1 inside {gpr_queue};
			rs2 inside {gpr_queue};
			rd inside  {gpr_queue};
		});
        
		// need set tr.pc here, following gen_br_target() will use this intruction's pc
		tr.pc = pc;

        if (tr.inst_type >= OP_JAL && tr.inst_type <= OP_BGEU) begin
			only_forward_jump = enable_backward_branch ? 0 : 1;
			result = gen_br_target(only_forward_jump, tr);
            if (result == 1) begin
                `uvm_info("debug", $psprintf("Gen br inst not successed, gen a ALU inst instead, pc = 0x%0x", tr.pc), UVM_HIGH);
                tr.inst_type = inst_type_e'($urandom_range('h0, 'h1d));
            end
		end
		else if (tr.inst_type >= OP_LB && tr.inst_type <= OP_SD) begin
            // min_addr/max_addr is useless here, set them to 0
			void'(gen_lsu_addr(0, 0, tr));
		end
		
        pa = 0;
		for (int i=0; i<get_fetch_size(tr.inst_type); i++) begin
			pa[64*i+:64] = get_pa(tr.pc+i, 1, 0);
		end
        if (tr.is_in_pc_pa_queue(pa) == 0) begin
            tr.pc_pa.push_back(pa);
        end

		inst_arr[tr.pc] = tr;

		gen_fail = 0;
        
        return tr;
    endfunction


	virtual task body();
		bit [63:0] m_pc;
		bit result;
		bit [63:0] m_start_pc;
        bit [63:0] last_pc;
        bit timeout_exit = 0;

        test_init();

		void'(this.randomize());
		`uvm_info("SEQ_LEN", $psprintf("seq_len = %0d\n", seqlen), UVM_NONE);
		m_start_pc = m_curr_pc;

        result = 1;
        while (result != 0) begin
            result = gen_valid_sequence(seqlen, last_pc);

		    if (result == 0) begin
		    	`uvm_info("debug", "valid sequence generated\n", UVM_HIGH);
		    end
		    else begin
				// check TB timeout
				curr_seconds = get_system_time();
				if ((curr_seconds - init_seconds) > timeout_seconds) begin
					`uvm_warning("warning", $psprintf("TB generation timeout, curr_seconds = %0d, init_seconds = %0d, delta_seconds = %0d", curr_seconds, init_seconds, curr_seconds-init_seconds));
                    timeout_exit = 1;
				end

		    	if (inst_arr.first(m_pc)) 
		    	do begin
                    if (!m_boot_pc.exists(m_pc) && !m_tvec_pc.exists(m_pc)) begin
		    			inst_arr.delete(m_pc);
		    		end
		    	end while (inst_arr.next(m_pc));
		    	m_curr_pc = m_start_pc;
                accessed_lsu_pa_arr.delete;

                if (timeout_exit == 0) begin
		    	    `uvm_info("debug", "can't generate valid sequence, re-randomize all", UVM_HIGH);
                end
                else begin
		    	    `uvm_info("debug", "can't generate valid sequence, exit with boot sequence", UVM_HIGH);
                    last_pc = min_pc;
                    break;
                end
		    end
        end

        m_curr_pc = last_pc;
        create_final_op();

		`uvm_info("end of body", $psprintf("inst_arr size = %0d\n", inst_arr.size()), UVM_NONE);
		
	endtask: body
endclass: riscv_random_all_seq

`endif

