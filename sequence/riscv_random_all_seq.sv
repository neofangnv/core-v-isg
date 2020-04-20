/*
 * Copyright (c) 2017, NVIDIA CORPORATION.  All rights reserved.
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

`ifndef RISCV_RANDOM_ALL_SEQ__SV
`define RISCV_RANDOM_ALL_SEQ__SV

// This is an example to show how to use random generator
// gen_inst() function should be overrided to implement corresponding constraint
// gen_valid_sequence() is the main function to generate a valid sequence
class riscv_random_all_seq extends riscv_base_seq;
	`uvm_object_utils(riscv_random_all_seq);

	riscv_inst_base_txn tr;

    bit enable_csr;
    bit increase_jalr;
    bit increase_ras;

    int insert_csr_freq;
    int jalr_weight;
    int ras_weight;

	function new (string name = "riscv_random_all_seq");
        super.new(name);

        if (!$value$plusargs("CSR_EN=%d", enable_csr)) begin
            enable_csr = 0;
        end
        if (!$value$plusargs("CSR_FREQ=%d", insert_csr_freq)) begin
            insert_csr_freq = 500;
        end
        if (!$value$plusargs("INCREASE_JALR=%d", increase_jalr)) begin
            increase_jalr = 0;
        end
        if (!$value$plusargs("JALR_WEIGHT=%d", jalr_weight)) begin
            jalr_weight = 40;
        end
        if (!$value$plusargs("INCREASE_RAS=%d", increase_ras)) begin
            increase_ras = 0;
        end
        if (!$value$plusargs("RAS_WEIGHT=%d", ras_weight)) begin
            ras_weight = 80;
        end
    endfunction: new
    
    // override original task to generate GPRs which are easy to produce valid IFU/LSU pa
    virtual task gen_init_gpr();
        c_gpr = new();
    	c_gpr.randomize() with {
            if (gen_rvc_en == 1) {
				// reduce possibility for RVC load/store exception
                (gpr[1][2:0] == 0) dist {0:/1, 1:/100};
                (gpr[7][2:0] == 0) dist {0:/1, 1:/10};
                (gpr[8][2:0] == 0) dist {0:/1, 1:/10};
                (gpr[9][2:0] == 0) dist {0:/1, 1:/10};
                (gpr[10][2:0] == 0) dist {0:/1, 1:/10};
                (gpr[11][2:0] == 0) dist {0:/1, 1:/10};
                (gpr[12][2:0] == 0) dist {0:/1, 1:/10};
                (gpr[13][2:0] == 0) dist {0:/1, 1:/10};
                (gpr[14][2:0] == 0) dist {0:/1, 1:/10};
            }
        };
    	for (int i=0; i<31; i++) begin
    		`uvm_info("INIT_GPR_DUMP", $psprintf("Initial randomized gpr[%0d] = 0x%0x\n", i+1, c_gpr.gpr[i]), UVM_HIGH);
    	end
    endtask


    // NEED_CHANGE, setup constraint as you want
	virtual function riscv_inst_base_txn gen_inst(bit[63:0] pc, bit gen_inst_32_en, ref bit gen_fail);
        bit [255:0] pa;
        bit result;

        tr = riscv_inst_base_txn::type_id::create("tr",,get_full_name());

        tr.randomize() with {
            if (gen_rvc_en == 0) {
                inst_type dist {OP_LUI:=15, OP_AUIPC:=15, OP_ADDI:=15, OP_SLTI:=5, OP_SLTIU:=5, OP_XORI:=5, OP_ORI:=5, OP_ANDI:=5, OP_SLLI:=5, OP_SRLI:=5, OP_SRAI:=5, OP_ADD:=15, OP_SUB:=15, OP_SLL:=5, OP_SLT:=5, OP_SLTU:=5, OP_XOR:=5, OP_SRL:=5, OP_SRA:=5, OP_OR:=5, OP_AND:=5, OP_ADDIW:=15, OP_SLLIW:=5, OP_SRLIW:=5, OP_SRAIW:=5, OP_ADDW:=15, OP_SUBW:=15, OP_SLLW:=5, OP_SRLW:=5, OP_SRAW:=5, OP_JAL:=10, OP_JALR:=5, ['h22:'h27]:/60, ['h30:'h3c]:/100, OP_LB:=5, OP_LBU:=5, OP_SB:=10, OP_LH:=5, OP_LHU:=5, OP_SH:=10, OP_LW:=5, OP_LWU:=5, OP_SW:=10, OP_LD:=10, OP_SD:=10, OP_WFI:=1, OP_ECALL:=1, OP_EBREAK:=1, OP_FENCE:=1, OP_FENCEI:=1, OP_SFENCE:=1};
            }
			else if (gen_inst_32_en == 0) {
                inst_type dist {OP_C_LWSP:=3, OP_C_LDSP:=3, OP_C_SWSP:=2, OP_C_SDSP:=2, OP_C_LW:=10, OP_C_LD:=10, OP_C_SW:=10, OP_C_SD:=10, OP_C_J:=10, OP_C_JR:=2, OP_C_JALR:=2, OP_C_BEQZ:=10, OP_C_BNEZ:=10, ['h120:'h123]:=5, OP_C_ADDI16SP:=1, ['h125:'h137]:=5, OP_C_NOP:=1, OP_C_EBREAK:=1};
			}
            else {
                inst_type dist {[0:'h1d]:/125, OP_JAL:=10, OP_JALR:=5, ['h22:'h27]:/60, ['h30:'h3c]:/100, OP_LB:=5, OP_LBU:=5, OP_SB:=10, OP_LH:=5, OP_LHU:=5, OP_SH:=10, OP_LW:=5, OP_LWU:=5, OP_SW:=10, OP_LD:=10, OP_SD:=10, OP_WFI:=1, OP_ECALL:=1, OP_EBREAK:=1, OP_FENCE:=1, OP_FENCEI:=1, OP_SFENCE:=1,
                OP_C_LWSP:=3, OP_C_LDSP:=3, OP_C_SWSP:=2, OP_C_SDSP:=2, OP_C_LW:=10, OP_C_LD:=10, OP_C_SW:=10, OP_C_SD:=10, OP_C_J:=10, OP_C_JR:=2, OP_C_JALR:=2, OP_C_BEQZ:=10, OP_C_BNEZ:=10, ['h120:'h123]:=10, OP_C_ADDI16SP:=1, ['h125:'h137]:=10, OP_C_NOP:=1, OP_C_EBREAK:=1};
            }

			rs1 inside gpr_queue;
			rs2 inside gpr_queue;
			rd inside gpr_queue;
            
			if (gen_rvc_en == 1) {
                (rd inside {1, 2, [8:15]}) dist {0:/5, 1:/1};
                (rd == 2) dist {0:/100, 1:/1};
            }
		};

        tr.pc = pc;

		gen_fail = 0;

        if (enable_csr == 1 && $urandom % insert_csr_freq == 0 && gen_inst_32_en == 1) begin
            `uvm_info("debug", $psprintf("generating a csr inst"), UVM_HIGH);

            tr.inst_type = $urandom_range('h50, 'h55);
            tr.randomize(csr) with {
			    if (m_curr_priv_level == PRIV_LEVEL_MMODE) {
                    csr dist {`CSR_MISA:=1, `CSR_MEDELEG:=10, `CSR_MIDELEG:=10, `CSR_MCYCLE:=1, `CSR_MCOUNTEREN:=0, `CSR_MSCRATCH:=5, `CSR_MEPC:=5, `CSR_MTVAL:=5, `CSR_SCOUNTEREN:=10, `CSR_SSCRATCH:=5, `CSR_SEPC:=5, `CSR_STVAL:=5, [`CSR_MHPMEVENT3:`CSR_MHPMEVENT10]:=1, [`CSR_MHPMCOUNTER3:`CSR_MHPMCOUNTER10]:/1};
                }
			    else if (m_curr_priv_level == PRIV_LEVEL_SMODE) {
                    csr dist {`CSR_SCOUNTEREN:=10, `CSR_SSCRATCH:=5, `CSR_SEPC:=5, `CSR_STVAL:=5};
                }
            };
			
			tr.rd = 0;
            tr.imm[16:5] = tr.csr;
        end
        else begin
            if ((tr.inst_type >= OP_JAL && tr.inst_type <= OP_BGEU) || (tr.inst_type >= OP_C_J && tr.inst_type <= OP_C_BNEZ)) begin
                if (increase_jalr == 1 && tr.inst_type != OP_JALR) begin
                    if (($urandom % 100) <= jalr_weight) begin
                        tr.inst_type = OP_JALR;
                        `uvm_info("debug", $psprintf("changing br inst to JALR"), UVM_HIGH);
                    end
                end

                // increase possibility for RAS push/pop inst
                if (increase_ras == 1) begin
                    if (($urandom % 100) <= ras_weight && !rsvd_gpr_arr.exists(1)) begin
                        tr.inst_type = ($urandom%2) ? OP_JALR : OP_JAL;
                        if ($urandom % 2 == 0) begin // RAS push
                            `uvm_info("debug", $psprintf("generating a RAS push inst"), UVM_HIGH);
                            tr.rd = 1;
                        end
                        else begin // RAS pop
                            `uvm_info("debug", $psprintf("generating a RAS pop inst"), UVM_HIGH);
                            tr.rs1 = 1;
                            tr.rd = 0;
                        end
                    end
                end
                else if (tr.inst_type == OP_JAL || tr.inst_type == OP_JALR) begin
                    if (!rsvd_gpr_arr.exists(1)) begin
                        if ($urandom % 10 == 0) begin // RAS push
                            `uvm_info("debug", $psprintf("generating a RAS push inst"), UVM_HIGH);
                            tr.rd = 1;
                        end
                        else if ($urandom % 10 == 1) begin // RAS pop
                            `uvm_info("debug", $psprintf("generating a RAS pop inst"), UVM_HIGH);
                            tr.rs1 = 1;
                            tr.rd = 0;
                        end
                    end
                end

		    	result = gen_br_target(0, tr);
                if (result == 1) begin
                    if (get_fetch_size(tr.inst_type) == 2) begin
                        `uvm_info("debug", $psprintf("Gen br inst not successed, gen a C ALU inst instead, pc = 0x%0x", tr.pc), UVM_HIGH);
                        tr.inst_type = $urandom_range('h132, 'h137);
                    end
                    else begin
                        `uvm_info("debug", $psprintf("Gen br inst not successed, gen a ALU inst instead, pc = 0x%0x", tr.pc), UVM_HIGH);
                        tr.inst_type = $urandom_range('h0, 'h1d);
                    end
                end
		    end
		    else if ((tr.inst_type >= OP_LB && tr.inst_type <= OP_SD) || (tr.inst_type >= OP_C_LWSP && tr.inst_type <= OP_C_SD) || tr.inst_type inside {OP_FLW, OP_FSW} ) begin
                // min_addr/max_addr is useless here, set them to 0
		    	gen_lsu_addr(0, 0, tr);
		    end
        end
		
        pa = 0;
		for (int i=0; i<get_fetch_size(tr.inst_type); i++) begin
			pa[64*i+:64] = get_pa(tr.pc+i, 1, 0);
		end
        if (tr.is_in_pc_pa_queue(pa) == 0) begin
            tr.pc_pa.push_back(pa);
        end

		inst_arr[tr.pc] = tr;
        
        return tr;
    endfunction


	virtual task body();
		bit [63:0] m_pc;
		bit result;
		bit [63:0] m_start_pc;
        bit [63:0] last_pc;
        bit timeout_exit = 0;

        test_init();

        // store inst_bin_code for boot inst
        if (inst_arr.first(m_pc)) 
		do begin
            if (m_boot_pc.exists(m_pc)) begin
                store_inst_code(inst_arr[m_pc]);
            end
		end while (inst_arr.next(m_pc));

		this.randomize();
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
        store_inst_code(inst_arr[last_pc]);

		`uvm_info("end of body", $psprintf("inst_arr size = %0d\n", inst_arr.size()), UVM_NONE);
		
	endtask: body
endclass: riscv_random_all_seq

`endif // RISCV_RANDOM_ALL_SEQ__SV
