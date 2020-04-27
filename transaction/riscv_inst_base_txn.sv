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

`ifndef RISCV_INST_BASE_TXN__SV
`define RISCV_INST_BASE_TXN__SV

typedef enum {
	 // ALU instructions
	 OP_LUI	= 'h0,
	 OP_AUIPC	= 'h1,
	 OP_ADDI	= 'h2,      //zz  
	 OP_SLTI	= 'h3,
	 OP_SLTIU  = 'h4,
	 OP_XORI   = 'h5,
	 OP_ORI    = 'h6,
	 OP_ANDI   = 'h7,
	 OP_SLLI   = 'h8,
	 OP_SRLI   = 'h9,
	 OP_SRAI   = 'ha,
	 OP_ADD    = 'hb,       //zz
	 OP_SUB    = 'hc,
	 OP_SLL    = 'hd,
	 OP_SLT    = 'he,
	 OP_SLTU   = 'hf,
	 OP_XOR    = 'h10,
	 OP_SRL    = 'h11,
	 OP_SRA    = 'h12,
	 OP_OR     = 'h13,
	 OP_AND    = 'h14,
	 OP_ADDIW  = 'h15,      //zz
	 OP_SLLIW  = 'h16,
	 OP_SRLIW  = 'h17,
	 OP_SRAIW  = 'h18,
	 OP_ADDW   = 'h19,      //zz
	 OP_SUBW   = 'h1a,
	 OP_SLLW   = 'h1b,
	 OP_SRLW   = 'h1c,
	 OP_SRAW   = 'h1d,

	 // branch instructions
	 OP_JAL    = 'h20,
	 OP_JALR   = 'h21,
	 OP_BEQ    = 'h22,
	 OP_BNE    = 'h23,
	 OP_BLT    = 'h24,
	 OP_BGE    = 'h25,
	 OP_BLTU   = 'h26,
	 OP_BGEU   = 'h27,

	 // MUL and DIV instructions
	 OP_MUL    = 'h30,
	 OP_MULH   = 'h31,
	 OP_MULHSU = 'h32,
	 OP_MULHU  = 'h33,
	 OP_DIV    = 'h34,
	 OP_DIVU   = 'h35,
	 OP_REM    = 'h36,
	 OP_REMU   = 'h37,
	 OP_MULW   = 'h38,
	 OP_DIVW   = 'h39,
	 OP_DIVUW  = 'h3a,
	 OP_REMW   = 'h3b,
	 OP_REMUW  = 'h3c,

	 // load and store instructions
	 OP_LB     = 'h40,
	 OP_LH     = 'h41,
	 OP_LW     = 'h42,
	 OP_LBU    = 'h43,
	 OP_LHU    = 'h44,
	 OP_SB     = 'h45,
	 OP_SH     = 'h46,
	 OP_SW     = 'h47,
	 OP_LWU    = 'h48,
	 OP_LD     = 'h49,
	 OP_SD     = 'h4a,

	 // CSR instructions
	 OP_CSRRW  = 'h50,
	 OP_CSRRS  = 'h51,
	 OP_CSRRC  = 'h52,
	 OP_CSRRWI = 'h53,
	 OP_CSRRSI = 'h54,
	 OP_CSRRCI = 'h55,

	 // special instructions
	 OP_FENCE  = 'h60,
	 OP_FENCEI = 'h61,
	 OP_ECALL  = 'h62,
	 OP_EBREAK = 'h63,
	 OP_MRET   = 'h64,
	 OP_WFI    = 'h65,
     OP_SRET   = 'h66,
     OP_SFENCE = 'h67,

    // fpu instructions for RV32F
    //load and store
    OP_FLW          = 'h70,
    OP_FSW          = 'h71,

    //compute
    OP_FADD_S       = 'h72,
    OP_FSUB_S       = 'h73,
    OP_FMUL_S       = 'h74,
    OP_FDIV_S       = 'h75,
    OP_FSQRT_S      = 'h76,
    OP_FMADD_S      = 'h77,
    OP_FMSUB_S      = 'h78,
    OP_FNMADD_S     = 'h79,
    OP_FNMSUB_S     = 'h7a,
    OP_FMIN_S       = 'h7b,
    OP_FMAX_S       = 'h7c,

    //cvt and mv inst
    OP_FMV_X_S      = 'h7d,
    OP_FMV_S_X      = 'h7e,
    OP_FCVT_W_S     = 'h7f,
    OP_FCVT_WU_S    = 'h80,
    OP_FCVT_S_W     = 'h81,
    OP_FCVT_S_WU    = 'h82,
    OP_FSGNJ_S      = 'h83,
    OP_FSGNJN_S     = 'h84,
    OP_FSGNJX_S     = 'h85,

    //compare
    OP_FEQ_S        = 'h86,
    OP_FLT_S        = 'h87,
    OP_FLE_S        = 'h88,
    OP_FCLASS_S     = 'h89,

    // fpu instructions for RV64F
    OP_FCVT_L_S     = 'h8a,
    OP_FCVT_LU_S    = 'h8b,
    OP_FCVT_S_L     = 'h8c,
    OP_FCVT_S_LU    = 'h8d,

    // illegal instructions
    OP_ILLEGAL      = 'hff,


    // RVC for RV64: Load-Store
    OP_C_LWSP       = 'h100,
    OP_C_LDSP       = 'h101,
    OP_C_SWSP       = 'h102,
    OP_C_SDSP       = 'h103,
    OP_C_LW         = 'h104,
    OP_C_LD         = 'h105,
    OP_C_SW         = 'h106,
    OP_C_SD         = 'h107,

    // RVC for RV64: Ctrl-Transfer
    OP_C_J          = 'h110,
    OP_C_JR         = 'h111,
    OP_C_JALR       = 'h112,
    OP_C_BEQZ       = 'h113,
    OP_C_BNEZ       = 'h114,

    // RVC for RV64: Integer-Cumputation
    OP_C_LI         = 'h120,
    OP_C_LUI        = 'h121,
    OP_C_ADDI       = 'h122,
    OP_C_ADDIW      = 'h123,
    OP_C_ADDI16SP   = 'h124,
    OP_C_ADDI4SPN   = 'h125,
    OP_C_SLLI       = 'h126,
    OP_C_SRLI       = 'h127,
    OP_C_SRAI       = 'h128,
    OP_C_ANDI       = 'h129,

    OP_C_MV         = 'h130,
    OP_C_ADD        = 'h131,
    OP_C_AND        = 'h132,
    OP_C_OR         = 'h133,
    OP_C_XOR        = 'h134,
    OP_C_SUB        = 'h135,
    OP_C_ADDW       = 'h136,
    OP_C_SUBW       = 'h137,

    OP_C_NOP        = 'h140,
    OP_C_EBREAK     = 'h141,

    // RVC for RV64: Illegal-instructions
    OP_C_ILLEGAL    = 'h1ff
} inst_type_e;

// Base RISCV instruction transaction class
// All specified instruction class will extend from this one
class riscv_inst_base_txn extends uvm_sequence_item;
	rand inst_type_e inst_type;
	static bit [63:0] instn=0;
	rand bit [ 4:0] rd;
	rand bit [ 4:0] rs1;
	rand bit [ 4:0] rs2;
	rand bit [ 4:0] rs3;
	rand bit [31:0] imm;
	rand bit [ 2:0] rm;
	rand bit [11:0] csr;
	rand bit [ 3:0] pred;
	rand bit [ 3:0] succ;
	bit [63:0] pc;
    bit [255:0] pc_pa[$];  // PA address for pc, 256-bit value is {PA(pc+3), PA(pc+2), PA(pc+1), PA(pc)}
	bit [31:0] inst_bin_code;
    int inst_bin_code_size;

	// indicate it's specially added/changed key instruction to avoid dead lock and other illegal condition
	// So don't override this instruction
	bit is_key_inst;

    // indicate it's ISR instruction
    bit is_isr_inst;

    // it's original store inst, but because it will write nearby after code address, change it to corresponding load inst
    bit is_change_store_inst;

    // indicate it's a c-extension instruction
    bit is_rvc_inst;

	// indicate it's a dummy instruction which pc_pa is illegal
	bit is_dummy_inst;

	// indicate that fpu inst is fixed to avoid changing gpr
	bit fpu_inst_is_fixed;

	// share used as branch target for branch instruction, and LSU VA for lsu instruction
	rand bit [63:0] target;
	rand bit [63:0] imm_64;

	// below is used for function coverage sample
	// gpr valid bit
	bit is_rs1_valid;
	bit is_rs2_valid;
	bit is_rs3_valid;
	bit is_rd_valid;

	// indicate what priviledge mode (M/S/U) after executing this instruction
	bit [1:0] result_mode;

	`uvm_object_utils_begin(riscv_inst_base_txn)
		`uvm_field_int(rd,                      UVM_ALL_ON)
		`uvm_field_int(rs1,                     UVM_ALL_ON)
		`uvm_field_int(rs2,                     UVM_ALL_ON)
		`uvm_field_int(rs3,                     UVM_ALL_ON)
		`uvm_field_int(rm,                      UVM_ALL_ON)
		`uvm_field_int(imm,                     UVM_ALL_ON)
		`uvm_field_int(csr,                     UVM_ALL_ON)
		`uvm_field_int(pc,                      UVM_ALL_ON)
		`uvm_field_queue_int(pc_pa,             UVM_ALL_ON)
		`uvm_field_int(pred,                    UVM_ALL_ON)
		`uvm_field_int(succ,                    UVM_ALL_ON)
		`uvm_field_int(inst_bin_code,           UVM_ALL_ON)
		`uvm_field_int(inst_bin_code_size,      UVM_ALL_ON)
		`uvm_field_int(is_key_inst,				UVM_ALL_ON)
		`uvm_field_int(is_isr_inst,				UVM_ALL_ON)
		`uvm_field_int(is_change_store_inst,	UVM_ALL_ON)
		`uvm_field_int(is_rvc_inst,				UVM_ALL_ON)
		`uvm_field_int(is_dummy_inst,			UVM_ALL_ON)
		`uvm_field_int(target,					UVM_ALL_ON)
		`uvm_field_int(imm_64,					UVM_ALL_ON)
        `uvm_field_enum(inst_type_e,inst_type,  UVM_ALL_ON)
	`uvm_object_utils_end

	// default constraints
    const bit [4:0] rvc_gprlist[8] = {8,9,10,11,12,13,14,15}; 

	constraint c_inst_c_ext {
		// Add constraint here
        solve inst_type before rd, rs1, rs2, rs3, imm, rm, csr, pred, succ;
        (inst_type == OP_C_ADD)         -> {rs2!=0; rs1 == rd;}
        (inst_type == OP_C_JALR)        -> {rs1!=0;}

        (inst_type == OP_C_MV)          -> {rs2!=0;}
        (inst_type == OP_C_JR)          -> {rs1!=0;}

        (inst_type == OP_C_ADDI4SPN)    -> {rd inside {rvc_gprlist}; imm[9:2] != 0;}
        (inst_type == OP_C_LW)          -> {rs1 inside {rvc_gprlist}; rd inside {rvc_gprlist};}
        (inst_type == OP_C_LD)          -> {rs1 inside {rvc_gprlist}; rd inside {rvc_gprlist};}

        // add extra rd constraint for OP_C_SW/OP_C_SD, it's useless for them, just for random flow support
        // otherwise when corresponding store is changed to load, previous randomized rd value (with store constraint) will be conflicted with new rd constraint (with load constraint)
        (inst_type == OP_C_SW)          -> {rs1 inside {rvc_gprlist}; rs2 inside {rvc_gprlist}; rd inside {rvc_gprlist};}
        (inst_type == OP_C_SD)          -> {rs1 inside {rvc_gprlist}; rs2 inside {rvc_gprlist}; rd inside {rvc_gprlist};}
        
        (inst_type == OP_C_ADDI)        -> {rd!=0; rd == rs1;}
        (inst_type == OP_C_ADDIW)       -> {rd!=0; rd == rs1;}
        (inst_type == OP_C_ADDI16SP)    -> {imm[9:4] != 0;}
        
        (inst_type == OP_C_LUI)         -> {imm[17:12] != 0; rd != 2;}

        (inst_type == OP_C_SRLI)        -> {rs1 inside {rvc_gprlist}; rd == rs1; imm[5:0] != 0;}
        (inst_type == OP_C_SRAI)        -> {rs1 inside {rvc_gprlist}; rd == rs1; imm[5:0] != 0;}
        (inst_type == OP_C_ANDI)        -> {rs1 inside {rvc_gprlist}; rd == rs1;}

        (inst_type == OP_C_SUB)         -> {rs1 inside {rvc_gprlist}; rs2 inside {rvc_gprlist}; rd == rs1;}
        (inst_type == OP_C_XOR)         -> {rs1 inside {rvc_gprlist}; rs2 inside {rvc_gprlist}; rd == rs1;}
        (inst_type == OP_C_OR)          -> {rs1 inside {rvc_gprlist}; rs2 inside {rvc_gprlist}; rd == rs1;}
        (inst_type == OP_C_AND)         -> {rs1 inside {rvc_gprlist}; rs2 inside {rvc_gprlist}; rd == rs1;}
        (inst_type == OP_C_SUBW)        -> {rs1 inside {rvc_gprlist}; rs2 inside {rvc_gprlist}; rd == rs1;}
        (inst_type == OP_C_ADDW)        -> {rs1 inside {rvc_gprlist}; rs2 inside {rvc_gprlist}; rd == rs1;}

        (inst_type == OP_C_BEQZ)        -> {rs1 inside {rvc_gprlist};}
        (inst_type == OP_C_BNEZ)        -> {rs1 inside {rvc_gprlist};}
        
        (inst_type == OP_C_SLLI)        -> {rd == rs1; imm[5:0] != 0;}
        (inst_type == OP_C_LWSP)        -> {rd != 0;}
        (inst_type == OP_C_LDSP)        -> {rd != 0;}
        
        // add extra rd constraint for OP_C_SWSP/OP_C_SDSP, it's useless for them, just for random flow support
        // otherwise when corresponding store is changed to load, previous randomized rd value (with store constraint) will be conflicted with new rd constraint (with load constraint)
        (inst_type == OP_C_SWSP)        -> {rd != 0;}
        (inst_type == OP_C_SDSP)        -> {rd != 0;}
    }


	extern function new(string name = "riscv_inst_base_txn");

	// convert the instruction transaction into instruction binary code
	extern virtual function bit[31:0] gen_inst_bin_code();

    // decode inst bin code to each operand
    extern function void inst_decode(bit[31:0] inst_code);

    // check whether input pc in pc_pa queue
    extern function bit is_in_pc_pa_queue(bit[255:0] addr);

    // check if it's c-extension instruction
    extern function bit is_c_extension_inst(bit[31:0] inst_code);

endclass : riscv_inst_base_txn

function riscv_inst_base_txn::new(string name = "riscv_inst_base_txn");
	super.new(name);
	is_key_inst = 0;
endfunction: new

function bit riscv_inst_base_txn::is_in_pc_pa_queue(bit[255:0] addr);
    bit found = 0;

    if (this.pc_pa.size() != 0) begin
        for (int i=0; i<this.pc_pa.size(); i++) begin
            if (this.pc_pa[i] == addr) begin
                found = 1;
                break;
            end
        end
    end

    return found;
endfunction

function bit[31:0] riscv_inst_base_txn::gen_inst_bin_code();
	if (this.inst_type == OP_LUI) begin
		this.inst_bin_code = (imm[31:12] << 12) + (rd << 7) + 7'b0110111;
	end
	else if (this.inst_type == OP_AUIPC) begin
		this.inst_bin_code = (imm[31:12] << 12) + (rd << 7) + 7'b0010111;
	end
	else if (this.inst_type == OP_ADDI) begin
		this.inst_bin_code = (imm[11:0] << 20) + (rs1 << 15) + (3'b000 << 12) + (rd << 7) + 7'b0010011;
	end
	else if (this.inst_type == OP_SLTI) begin
		this.inst_bin_code = (imm[11:0] << 20) + (rs1 << 15) + (3'b010 << 12) + (rd << 7) + 7'b0010011;
	end
	else if (this.inst_type == OP_SLTIU) begin
		this.inst_bin_code = (imm[11:0] << 20) + (rs1 << 15) + (3'b011 << 12) + (rd << 7) + 7'b0010011;
	end
	else if (this.inst_type == OP_XORI) begin
		this.inst_bin_code = (imm[11:0] << 20) + (rs1 << 15) + (3'b100 << 12) + (rd << 7) + 7'b0010011;
	end
	else if (this.inst_type == OP_ORI) begin
		this.inst_bin_code = (imm[11:0] << 20) + (rs1 << 15) + (3'b110 << 12) + (rd << 7) + 7'b0010011;
	end
	else if (this.inst_type == OP_ANDI) begin
		this.inst_bin_code = (imm[11:0] << 20) + (rs1 << 15) + (3'b111 << 12) + (rd << 7) + 7'b0010011;
	end
	else if (this.inst_type == OP_SLLI) begin
		this.inst_bin_code = (6'b000000 << 26) + (imm[5:0] << 20) + (rs1 << 15) + (3'b001 << 12) + (rd << 7) + 7'b0010011;
	end
	else if (this.inst_type == OP_SRLI) begin
		this.inst_bin_code = (6'b000000 << 26) + (imm[5:0] << 20) + (rs1 << 15) + (3'b101 << 12) + (rd << 7) + 7'b0010011;
	end
	else if (this.inst_type == OP_SRAI) begin
		this.inst_bin_code = (6'b010000 << 26) + (imm[5:0] << 20) + (rs1 << 15) + (3'b101 << 12) + (rd << 7) + 7'b0010011;
	end
	else if (this.inst_type == OP_ADD) begin
		this.inst_bin_code = (7'b0000000 << 25) + (rs2 << 20) + (rs1 << 15) + (3'b000 << 12) + (rd << 7) + 7'b0110011;
	end
	else if (this.inst_type == OP_SUB) begin
		this.inst_bin_code = (7'b0100000 << 25) + (rs2 << 20) + (rs1 << 15) + (3'b000 << 12) + (rd << 7) + 7'b0110011;
	end
	else if (this.inst_type == OP_SLL) begin
		this.inst_bin_code = (7'b0000000 << 25) + (rs2 << 20) + (rs1 << 15) + (3'b001 << 12) + (rd << 7) + 7'b0110011;
	end
	else if (this.inst_type == OP_SLT) begin
		this.inst_bin_code = (7'b0000000 << 25) + (rs2 << 20) + (rs1 << 15) + (3'b010 << 12) + (rd << 7) + 7'b0110011;
	end
	else if (this.inst_type == OP_SLTU) begin
		this.inst_bin_code = (7'b0000000 << 25) + (rs2 << 20) + (rs1 << 15) + (3'b011 << 12) + (rd << 7) + 7'b0110011;
	end
	else if (this.inst_type == OP_XOR) begin
		this.inst_bin_code = (7'b0000000 << 25) + (rs2 << 20) + (rs1 << 15) + (3'b100 << 12) + (rd << 7) + 7'b0110011;
	end
	else if (this.inst_type == OP_SRL) begin
		this.inst_bin_code = (7'b0000000 << 25) + (rs2 << 20) + (rs1 << 15) + (3'b101 << 12) + (rd << 7) + 7'b0110011;
	end
	else if (this.inst_type == OP_SRA) begin
		this.inst_bin_code = (7'b0100000 << 25) + (rs2 << 20) + (rs1 << 15) + (3'b101 << 12) + (rd << 7) + 7'b0110011;
	end
	else if (this.inst_type == OP_OR) begin
		this.inst_bin_code = (7'b0000000 << 25) + (rs2 << 20) + (rs1 << 15) + (3'b110 << 12) + (rd << 7) + 7'b0110011;
	end
	else if (this.inst_type == OP_AND) begin
		this.inst_bin_code = (7'b0000000 << 25) + (rs2 << 20) + (rs1 << 15) + (3'b111 << 12) + (rd << 7) + 7'b0110011;
	end
	else if (this.inst_type == OP_ADDIW) begin
		this.inst_bin_code = (imm[11:0] << 20) + (rs1 << 15) + (3'b000 << 12) + (rd << 7) + 7'b0011011;
	end
	else if (this.inst_type == OP_SLLIW) begin
		this.inst_bin_code = (7'b0000000 << 25) + (imm[4:0] << 20) + (rs1 << 15) + (3'b001 << 12) + (rd << 7) + 7'b0011011;
	end
	else if (this.inst_type == OP_SRLIW) begin
		this.inst_bin_code = (7'b0000000 << 25) + (imm[4:0] << 20) + (rs1 << 15) + (3'b101 << 12) + (rd << 7) + 7'b0011011;
	end
	else if (this.inst_type == OP_SRAIW) begin
		this.inst_bin_code = (7'b0100000 << 25) + (imm[4:0] << 20) + (rs1 << 15) + (3'b101 << 12) + (rd << 7) + 7'b0011011;
	end
	else if (this.inst_type == OP_ADDW) begin
		this.inst_bin_code = (7'b0000000 << 25) + (rs2 << 20) + (rs1 << 15) + (3'b000 << 12) + (rd << 7) + 7'b0111011;
	end
	else if (this.inst_type == OP_SUBW) begin
		this.inst_bin_code = (7'b0100000 << 25) + (rs2 << 20) + (rs1 << 15) + (3'b000 << 12) + (rd << 7) + 7'b0111011;
	end
	else if (this.inst_type == OP_SLLW) begin
		this.inst_bin_code = (7'b0000000 << 25) + (rs2 << 20) + (rs1 << 15) + (3'b001 << 12) + (rd << 7) + 7'b0111011;
	end
	else if (this.inst_type == OP_SRLW) begin
		this.inst_bin_code = (7'b0000000 << 25) + (rs2 << 20) + (rs1 << 15) + (3'b101 << 12) + (rd << 7) + 7'b0111011;
	end
	else if (this.inst_type == OP_SRAW) begin
		this.inst_bin_code = (7'b0100000 << 25) + (rs2 << 20) + (rs1 << 15) + (3'b101 << 12) + (rd << 7) + 7'b0111011;
	end
	else if (this.inst_type == OP_JAL) begin
		this.inst_bin_code = ({imm[20], imm[10:1], imm[11], imm[19:12]} << 12) + (rd << 7) + 7'b1101111;
	end
	else if (this.inst_type == OP_JALR) begin
		this.inst_bin_code = (imm[11:0] << 20) + (rs1 << 15) + (3'b000 << 12) + (rd << 7) + 7'b1100111;
	end
	else if (this.inst_type == OP_BEQ) begin
		this.inst_bin_code = ({imm[12], imm[10:5]} << 25) + (rs2 << 20) + (rs1 << 15) + (3'b000 << 12) + ({imm[4:1], imm[11]} << 7) + 7'b1100011;
	end
	else if (this.inst_type == OP_BNE) begin
		this.inst_bin_code = ({imm[12], imm[10:5]} << 25) + (rs2 << 20) + (rs1 << 15) + (3'b001 << 12) + ({imm[4:1], imm[11]} << 7) + 7'b1100011;
	end
	else if (this.inst_type == OP_BLT) begin
		this.inst_bin_code = ({imm[12], imm[10:5]} << 25) + (rs2 << 20) + (rs1 << 15) + (3'b100 << 12) + ({imm[4:1], imm[11]} << 7) + 7'b1100011;
	end
	else if (this.inst_type == OP_BGE) begin
		this.inst_bin_code = ({imm[12], imm[10:5]} << 25) + (rs2 << 20) + (rs1 << 15) + (3'b101 << 12) + ({imm[4:1], imm[11]} << 7) + 7'b1100011;
	end
	else if (this.inst_type == OP_BLTU) begin
		this.inst_bin_code = ({imm[12], imm[10:5]} << 25) + (rs2 << 20) + (rs1 << 15) + (3'b110 << 12) + ({imm[4:1], imm[11]} << 7) + 7'b1100011;
	end
	else if (this.inst_type == OP_BGEU) begin
		this.inst_bin_code = ({imm[12], imm[10:5]} << 25) + (rs2 << 20) + (rs1 << 15) + (3'b111 << 12) + ({imm[4:1], imm[11]} << 7) + 7'b1100011;
	end
	else if (this.inst_type == OP_MUL) begin
		this.inst_bin_code = (7'b0000001 << 25) + (rs2 << 20) + (rs1 << 15) + (3'b000 << 12) + (rd << 7) + 7'b0110011;
	end
	else if (this.inst_type == OP_MULH) begin
		this.inst_bin_code = (7'b0000001 << 25) + (rs2 << 20) + (rs1 << 15) + (3'b001 << 12) + (rd << 7) + 7'b0110011;
	end
	else if (this.inst_type == OP_MULHSU) begin
		this.inst_bin_code = (7'b0000001 << 25) + (rs2 << 20) + (rs1 << 15) + (3'b010 << 12) + (rd << 7) + 7'b0110011;
	end
	else if (this.inst_type == OP_MULHU) begin
		this.inst_bin_code = (7'b0000001 << 25) + (rs2 << 20) + (rs1 << 15) + (3'b011 << 12) + (rd << 7) + 7'b0110011;
	end
	else if (this.inst_type == OP_DIV) begin
		this.inst_bin_code = (7'b0000001 << 25) + (rs2 << 20) + (rs1 << 15) + (3'b100 << 12) + (rd << 7) + 7'b0110011;
	end
	else if (this.inst_type == OP_DIVU) begin
		this.inst_bin_code = (7'b0000001 << 25) + (rs2 << 20) + (rs1 << 15) + (3'b101 << 12) + (rd << 7) + 7'b0110011;
	end
	else if (this.inst_type == OP_REM) begin
		this.inst_bin_code = (7'b0000001 << 25) + (rs2 << 20) + (rs1 << 15) + (3'b110 << 12) + (rd << 7) + 7'b0110011;
	end
	else if (this.inst_type == OP_REMU) begin
		this.inst_bin_code = (7'b0000001 << 25) + (rs2 << 20) + (rs1 << 15) + (3'b111 << 12) + (rd << 7) + 7'b0110011;
	end
	else if (this.inst_type == OP_MULW) begin
		this.inst_bin_code = (7'b0000001 << 25) + (rs2 << 20) + (rs1 << 15) + (3'b000 << 12) + (rd << 7) + 7'b0111011;
	end
	else if (this.inst_type == OP_DIVW) begin
		this.inst_bin_code = (7'b0000001 << 25) + (rs2 << 20) + (rs1 << 15) + (3'b100 << 12) + (rd << 7) + 7'b0111011;
	end
	else if (this.inst_type == OP_DIVUW) begin
		this.inst_bin_code = (7'b0000001 << 25) + (rs2 << 20) + (rs1 << 15) + (3'b101 << 12) + (rd << 7) + 7'b0111011;
	end
	else if (this.inst_type == OP_REMW) begin
		this.inst_bin_code = (7'b0000001 << 25) + (rs2 << 20) + (rs1 << 15) + (3'b110 << 12) + (rd << 7) + 7'b0111011;
	end
	else if (this.inst_type == OP_REMUW) begin
		this.inst_bin_code = (7'b0000001 << 25) + (rs2 << 20) + (rs1 << 15) + (3'b111 << 12) + (rd << 7) + 7'b0111011;
	end
	else if (this.inst_type == OP_LB) begin
		this.inst_bin_code = (imm[11:0] << 20) + (rs1 << 15) + (3'b000 << 12) + (rd << 7) + 7'b0000011;
	end
	else if (this.inst_type == OP_LH) begin
		this.inst_bin_code = (imm[11:0] << 20) + (rs1 << 15) + (3'b001 << 12) + (rd << 7) + 7'b0000011;
	end
	else if (this.inst_type == OP_LW) begin
		this.inst_bin_code = (imm[11:0] << 20) + (rs1 << 15) + (3'b010 << 12) + (rd << 7) + 7'b0000011;
	end
	else if (this.inst_type == OP_LBU) begin
		this.inst_bin_code = (imm[11:0] << 20) + (rs1 << 15) + (3'b100 << 12) + (rd << 7) + 7'b0000011;
	end
	else if (this.inst_type == OP_LHU) begin
		this.inst_bin_code = (imm[11:0] << 20) + (rs1 << 15) + (3'b101 << 12) + (rd << 7) + 7'b0000011;
	end
	else if (this.inst_type == OP_SB) begin
		this.inst_bin_code = (imm[11:5] << 25) + (rs2 << 20) + (rs1 << 15) + (3'b000 << 12) + (imm[4:0] << 7) + 7'b0100011;
	end
	else if (this.inst_type == OP_SH) begin
		this.inst_bin_code = (imm[11:5] << 25) + (rs2 << 20) + (rs1 << 15) + (3'b001 << 12) + (imm[4:0] << 7) + 7'b0100011;
	end
	else if (this.inst_type == OP_SW) begin
		this.inst_bin_code = (imm[11:5] << 25) + (rs2 << 20) + (rs1 << 15) + (3'b010 << 12) + (imm[4:0] << 7) + 7'b0100011;
	end
	else if (this.inst_type == OP_LWU) begin
		this.inst_bin_code = (imm[11:0] << 20) + (rs1 << 15) + (3'b110 << 12) + (rd << 7) + 7'b0000011;
	end
	else if (this.inst_type == OP_LD) begin
		this.inst_bin_code = (imm[11:0] << 20) + (rs1 << 15) + (3'b011 << 12) + (rd << 7) + 7'b0000011;
	end
	else if (this.inst_type == OP_SD) begin
		this.inst_bin_code = (imm[11:5] << 25) + (rs2 << 20) + (rs1 << 15) + (3'b011 << 12) + (imm[4:0] << 7) + 7'b0100011;
	end
	else if (this.inst_type == OP_CSRRW) begin
		this.inst_bin_code = (csr << 20) + (rs1 << 15) + (3'b001 << 12) + (rd << 7) + 7'b1110011;
	end
	else if (this.inst_type == OP_CSRRS) begin
		this.inst_bin_code = (csr << 20) + (rs1 << 15) + (3'b010 << 12) + (rd << 7) + 7'b1110011;
	end
	else if (this.inst_type == OP_CSRRC) begin
		this.inst_bin_code = (csr << 20) + (rs1 << 15) + (3'b011 << 12) + (rd << 7) + 7'b1110011;
	end
	else if (this.inst_type == OP_CSRRWI) begin
		this.inst_bin_code = (csr << 20) + (imm[4:0] << 15) + (3'b101 << 12) + (rd << 7) + 7'b1110011;
	end
	else if (this.inst_type == OP_CSRRSI) begin
		this.inst_bin_code = (csr << 20) + (imm[4:0] << 15) + (3'b110 << 12) + (rd << 7) + 7'b1110011;
	end
	else if (this.inst_type == OP_CSRRCI) begin
		this.inst_bin_code = (csr << 20) + (imm[4:0] << 15) + (3'b111 << 12) + (rd << 7) + 7'b1110011;
	end
	else if (this.inst_type == OP_FENCE) begin
		this.inst_bin_code = (4'b0000 << 28) + (pred << 24) + (succ << 20) + (5'b00000 << 15) + (3'b000 << 12) + (5'b00000 << 7) + 7'b0001111;
	end
	else if (this.inst_type == OP_FENCEI) begin
		this.inst_bin_code = (4'b0000 << 28) + (4'b0000 << 24) + (4'b0000 << 20) + (5'b00000 << 15) + (3'b001 << 12) + (5'b00000 << 7) + 7'b0001111;
	end
	else if (this.inst_type == OP_ECALL) begin
		this.inst_bin_code = (12'b000000000000 << 20) + (5'b00000 << 15) + (3'b000 << 12) + (5'b00000 << 7) + 7'b1110011;
	end
	else if (this.inst_type == OP_EBREAK) begin
		this.inst_bin_code = (12'b000000000001 << 20) + (5'b00000 << 15) + (3'b000 << 12) + (5'b00000 << 7) + 7'b1110011;
	end
	else if (this.inst_type == OP_MRET) begin
		this.inst_bin_code = (12'b001100000010 << 20) + (5'b00000 << 15) + (3'b000 << 12) + (5'b00000 << 7) + 7'b1110011;
	end
	else if (this.inst_type == OP_WFI) begin
		this.inst_bin_code = (12'b000100000101 << 20) + (5'b00000 << 15) + (3'b000 << 12) + (5'b00000 << 7) + 7'b1110011;
	end
	else if (this.inst_type == OP_SRET) begin
		this.inst_bin_code = (12'b000100000010 << 20) + (5'b00000 << 15) + (3'b000 << 12) + (5'b00000 << 7) + 7'b1110011;
	end
	else if (this.inst_type == OP_SFENCE) begin
		this.inst_bin_code = (7'b0001001 << 25) + (rs2 << 20) + (rs1 << 15) + (3'b000 << 12) + (5'b00000 << 7) + 7'b1110011;
	end
    else if (this.inst_type == OP_FLW) begin
		this.inst_bin_code = (imm[11:0] << 20) + (rs1 << 15) + (3'b010 << 12) + (rd << 7) + 7'b000_0111;
    end else if (this.inst_type == OP_FSW) begin
		this.inst_bin_code = (imm[11:5] << 25) + (rs2 << 20) + (rs1 << 15) + (3'b010 << 12) + (imm[4:0] << 7) + 7'b010_0111;
    end else if (this.inst_type == OP_FADD_S) begin
		this.inst_bin_code = (7'b000_0000 << 25) + (rs2 << 20) + (rs1 << 15) + (rm << 12) + (rd << 7) + 7'b101_0011;
	end else if (this.inst_type == OP_FSUB_S) begin
		this.inst_bin_code = (7'b000_0100 << 25) + (rs2 << 20) + (rs1 << 15) + (rm << 12) + (rd << 7) + 7'b101_0011;
	end else if (this.inst_type == OP_FMUL_S) begin
		this.inst_bin_code = (7'b000_1000 << 25) + (rs2 << 20) + (rs1 << 15) + (rm << 12) + (rd << 7) + 7'b101_0011;
	end else if (this.inst_type == OP_FDIV_S) begin
		this.inst_bin_code = (7'b000_1100 << 25) + (rs2 << 20) + (rs1 << 15) + (rm << 12) + (rd << 7) + 7'b101_0011;
	end else if (this.inst_type == OP_FSQRT_S) begin
		this.inst_bin_code = (7'b010_1100 << 25) + (5'b0_0000 << 20) + (rs1 << 15) + (rm << 12) + (rd << 7) + 7'b101_0011;
    end else if (this.inst_type == OP_FSGNJ_S) begin
		this.inst_bin_code = (7'b001_0000 << 25) + (rs2 << 20) + (rs1 << 15) + (3'b000 << 12) + (rd << 7) + 7'b101_0011;
    end else if (this.inst_type == OP_FSGNJN_S) begin
		this.inst_bin_code = (7'b001_0000 << 25) + (rs2 << 20) + (rs1 << 15) + (3'b001 << 12) + (rd << 7) + 7'b101_0011;
    end else if (this.inst_type == OP_FSGNJX_S) begin
		this.inst_bin_code = (7'b001_0000 << 25) + (rs2 << 20) + (rs1 << 15) + (3'b010 << 12) + (rd << 7) + 7'b101_0011;
    end else if (this.inst_type == OP_FMADD_S) begin
		this.inst_bin_code = (rs3 << 27) + (2'b00 << 25) + (rs2 << 20) + (rs1 << 15) + (rm << 12) + (rd << 7) + 7'b100_0011;
    end else if (this.inst_type == OP_FMSUB_S) begin
		this.inst_bin_code = (rs3 << 27) + (2'b00 << 25) + (rs2 << 20) + (rs1 << 15) + (rm << 12) + (rd << 7) + 7'b100_0111;
    end else if (this.inst_type == OP_FNMADD_S) begin
		this.inst_bin_code = (rs3 << 27) + (2'b00 << 25) + (rs2 << 20) + (rs1 << 15) + (rm << 12) + (rd << 7) + 7'b100_1111;
    end else if (this.inst_type == OP_FNMSUB_S) begin
		this.inst_bin_code = (rs3 << 27) + (2'b00 << 25) + (rs2 << 20) + (rs1 << 15) + (rm << 12) + (rd << 7) + 7'b100_1011;
    end else if (this.inst_type == OP_FMIN_S) begin
		this.inst_bin_code = (7'b001_0100 << 25) + (rs2 << 20) + (rs1 << 15) + (3'b000 << 12) + (rd << 7) + 7'b101_0011;
    end else if (this.inst_type == OP_FMAX_S) begin
		this.inst_bin_code = (7'b001_0100 << 25) + (rs2 << 20) + (rs1 << 15) + (3'b001 << 12) + (rd << 7) + 7'b101_0011;
	end else if (this.inst_type == OP_FMV_X_S) begin
		this.inst_bin_code = (7'b111_0000 << 25) + (5'b0_0000 << 20) + (rs1 << 15) + (3'b000 << 12) + (rd << 7) + 7'b101_0011;
	end else if (this.inst_type == OP_FMV_S_X) begin
		this.inst_bin_code = (7'b111_1000 << 25) + (5'b0_0000 << 20) + (rs1 << 15) + (3'b000 << 12) + (rd << 7) + 7'b101_0011;
    end else if (this.inst_type == OP_FEQ_S) begin
		this.inst_bin_code = (7'b101_0000 << 25) + (rs2 << 20) + (rs1 << 15) + (3'b010 << 12) + (rd << 7) + 7'b101_0011;
    end else if (this.inst_type == OP_FLT_S) begin
		this.inst_bin_code = (7'b101_0000 << 25) + (rs2 << 20) + (rs1 << 15) + (3'b001 << 12) + (rd << 7) + 7'b101_0011;
    end else if (this.inst_type == OP_FLE_S) begin
		this.inst_bin_code = (7'b101_0000 << 25) + (rs2 << 20) + (rs1 << 15) + (3'b000 << 12) + (rd << 7) + 7'b101_0011;
	end else if (this.inst_type == OP_FCLASS_S) begin
		this.inst_bin_code = (7'b111_0000 << 25) + (5'b0_0000 << 20) + (rs1 << 15) + (3'b001 << 12) + (rd << 7) + 7'b101_0011;
	end else if (this.inst_type == OP_FCVT_W_S) begin
		this.inst_bin_code = (7'b110_0000 << 25) + (5'b0_0000 << 20) + (rs1 << 15) + (rm << 12) + (rd << 7) + 7'b101_0011;
	end else if (this.inst_type == OP_FCVT_WU_S) begin
		this.inst_bin_code = (7'b110_0000 << 25) + (5'b0_0001 << 20) + (rs1 << 15) + (rm << 12) + (rd << 7) + 7'b101_0011;
	end else if (this.inst_type == OP_FCVT_S_W) begin
		this.inst_bin_code = (7'b110_1000 << 25) + (5'b0_0000 << 20) + (rs1 << 15) + (rm << 12) + (rd << 7) + 7'b101_0011;
	end else if (this.inst_type == OP_FCVT_S_WU) begin
		this.inst_bin_code = (7'b110_1000 << 25) + (5'b0_0001 << 20) + (rs1 << 15) + (rm << 12) + (rd << 7) + 7'b101_0011;
	end else if (this.inst_type == OP_FCVT_L_S) begin
		this.inst_bin_code = (7'b110_0000 << 25) + (5'b0_0010 << 20) + (rs1 << 15) + (rm << 12) + (rd << 7) + 7'b101_0011;
	end else if (this.inst_type == OP_FCVT_LU_S) begin
		this.inst_bin_code = (7'b110_0000 << 25) + (5'b0_0011 << 20) + (rs1 << 15) + (rm << 12) + (rd << 7) + 7'b101_0011;
	end else if (this.inst_type == OP_FCVT_S_L) begin
		this.inst_bin_code = (7'b110_1000 << 25) + (5'b0_0010 << 20) + (rs1 << 15) + (rm << 12) + (rd << 7) + 7'b101_0011;
	end else if (this.inst_type == OP_FCVT_S_LU) begin
		this.inst_bin_code = (7'b110_1000 << 25) + (5'b0_0011 << 20) + (rs1 << 15) + (rm << 12) + (rd << 7) + 7'b101_0011;
    end else if (this.inst_type == OP_C_ADDI4SPN) begin
        this.inst_bin_code = (3'b000<<13) + (imm[5:4]<<11) + (imm[9:6]<<7) + (imm[2]<<6) + (imm[3]<<5) + (rd[2:0]<<2) + 2'b00;          //imm -> nzimm
//DFP    end else if (this.inst_type == OP_C_FLD) begin
//DFP        this.inst_bin_code = (3'b001<<13) + (imm[5:3]<<10) + (rs1[2:0]<<7) + (imm[7:6]<<5) + (rd[2:0]<<2) + 2'b00;
//RV128    end else if (this.inst_type == OP_C_LQ) begin
//RV128        this.inst_bin_code = (3'b001<<13) + (imm[5:4]<<11) + (imm[8]<<10) + (rs1[2:0]<<7) + (imm[7:6]<<5) + (rd[2:0]<<2) + 2'b00;
    end else if (this.inst_type == OP_C_LW) begin
        this.inst_bin_code = (3'b010<<13) + (imm[5:3]<<10) + (rs1[2:0]<<7) + (imm[2]<<6) + (imm[6]<<5) + (rd[2:0]<<2) + 2'b00;
//RV32    end else if (this.inst_type == OP_C_FLW) begin
//RV32        this.inst_bin_code = (3'b011<<13) + (imm[5:3]<<10) + (rs1[2:0]<<7) + (imm[2]<<6) + (imm[6]<<5) + (rd[2:0]<<2) + 2'b00;
    end else if (this.inst_type == OP_C_LD) begin
        this.inst_bin_code = (3'b011<<13) + (imm[5:3]<<10) + (rs1[2:0]<<7) + (imm[7:6]<<5) + (rd[2:0]<<2) + 2'b00;
//DFP    end else if (this.inst_type == OP_C_FSD) begin
//DFP        this.inst_bin_code = (3'b101<<13) + (imm[5:3]<<10) + (rs1[2:0]<<7) + (imm[7:6]<<5) + (rs2[2:0]<<2) + 2'b00;
//RV128    end else if (this.inst_type == OP_C_SQ) begin
//RV128        this.inst_bin_code = (3'b101<<13) + (imm[5:4]<<11) + (imm[8]<<10) + (rs1[2:0]<<7) + (imm[7:6]<<5) + (rs2[2:0]<<2) + 2'b00;
    end else if (this.inst_type == OP_C_SW) begin
        this.inst_bin_code = (3'b110<<13) + (imm[5:3]<<10) + (rs1[2:0]<<7) + (imm[2]<<6) + (imm[6]<<5) + (rs2[2:0]<<2) + 2'b00;
//RV32    end else if (this.inst_type == OP_C_FSW) begin
//RV32        this.inst_bin_code = (3'b111<<13) + (imm[5:3]<<10) + (rs1[2:0]<<7) + (imm[2]<<6) + (imm[6]<<5) + (rs2[2:0]<<2) + 2'b00;
    end else if (this.inst_type == OP_C_SD) begin
        this.inst_bin_code = (3'b111<<13) + (imm[5:3]<<10) + (rs1[2:0]<<7) + (imm[7:6]<<5) + (rs2[2:0]<<2) + 2'b00;
    end else if (this.inst_type == OP_C_NOP) begin
        this.inst_bin_code = (3'b000<<13) + (1'b0<<12) + (5'b00000<<7) + (5'b00000<<2) + 2'b01;
    end else if (this.inst_type == OP_C_ADDI) begin
        this.inst_bin_code = (3'b000<<13) + (imm[5]<<12) + (rs1<<7) + (imm[4:0]<<2) + 2'b01;                          //imm -> nzimm          //rs1/rd!=0.  TODO/FIXME
//RV32    end else if (this.inst_type == OP_C_JAL) begin
//RV32        this.inst_bin_code = (3'b001<<13) + (imm[11]<<12) + (imm[4]<<11) + (imm[9:8]<<9) + (imm[10]<<8) + (imm[6]<<7) + (imm[7]<<6) + (imm[3:1]<<3) + (imm[5]<<2) + 2'b01;      //offset
    end else if (this.inst_type == OP_C_ADDIW) begin
        this.inst_bin_code = (3'b001<<13) + (imm[5]<<12) + (rs1<<7) + (imm[4:0]<<2) + 2'b01;                          
    end else if (this.inst_type == OP_C_LI) begin
        this.inst_bin_code = (3'b010<<13) + (imm[5]<<12) + (rd<<7) + (imm[4:0]<<2) + 2'b01;                          
    end else if (this.inst_type == OP_C_ADDI16SP) begin
        this.inst_bin_code = (3'b011<<13) + (imm[9]<<12) + (5'd2<<7) + (imm[4]<<6) + (imm[6]<<5) + (imm[8:7]<<3) + (imm[5]<<2) + 2'b01;
    end else if (this.inst_type == OP_C_LUI) begin
        this.inst_bin_code = (3'b011<<13) + (imm[17]<<12) + (rd<<7) + (imm[16:12]<<2) + 2'b01;                         
    end else if (this.inst_type == OP_C_SRLI) begin
        this.inst_bin_code = (3'b100<<13) + (imm[5]<<12) + (2'b00<<10) + (rs1[2:0]<<7) + (imm[4:0]<<2) + 2'b01;
//    end else if (this.inst_type == OP_C_SRLI64) begin
//        this.inst_bin_code = (3'b100<<13) + (1'b0<<12) + (2'b00<<10) + (rs1[2:0]<<7) + (5'b00000<2) + 2'b01;
    end else if (this.inst_type == OP_C_SRAI) begin
        this.inst_bin_code = (3'b100<<13) + (imm[5]<<12) + (2'b01<<10) + (rs1[2:0]<<7) + (imm[4:0]<<2) + 2'b01;
//    end else if (this.inst_type == OP_C_SRAI64) begin
//        this.inst_bin_code = (3'b100<<13) + (1'b0<<12) + (2'b01<<10) + (rs1[2:0]<<7) + (5'b00000<2) + 2'b01;
    end else if (this.inst_type == OP_C_ANDI) begin
        this.inst_bin_code = (3'b100<<13) + (imm[5]<<12) + (2'b10<<10) + (rs1[2:0]<<7) + (imm[4:0]<<2) + 2'b01;
    end else if (this.inst_type == OP_C_SUB) begin
        this.inst_bin_code = (3'b100<<13) + (1'b0<<12) + (2'b11<<10) + (rs1[2:0]<<7) + (2'b00<<5) + (rs2[2:0]<<2) + 2'b01;
    end else if (this.inst_type == OP_C_XOR) begin
        this.inst_bin_code = (3'b100<<13) + (1'b0<<12) + (2'b11<<10) + (rs1[2:0]<<7) + (2'b01<<5) + (rs2[2:0]<<2) + 2'b01;
    end else if (this.inst_type == OP_C_OR) begin
        this.inst_bin_code = (3'b100<<13) + (1'b0<<12) + (2'b11<<10) + (rs1[2:0]<<7) + (2'b10<<5) + (rs2[2:0]<<2) + 2'b01;
    end else if (this.inst_type == OP_C_AND) begin
        this.inst_bin_code = (3'b100<<13) + (1'b0<<12) + (2'b11<<10) + (rs1[2:0]<<7) + (2'b11<<5) + (rs2[2:0]<<2) + 2'b01;
    end else if (this.inst_type == OP_C_SUBW) begin
        this.inst_bin_code = (3'b100<<13) + (1'b1<<12) + (2'b11<<10) + (rs1[2:0]<<7) + (2'b00<<5) + (rs2[2:0]<<2) + 2'b01;
    end else if (this.inst_type == OP_C_ADDW) begin
        this.inst_bin_code = (3'b100<<13) + (1'b1<<12) + (2'b11<<10) + (rs1[2:0]<<7) + (2'b01<<5) + (rs2[2:0]<<2) + 2'b01;
    end else if (this.inst_type == OP_C_J) begin
        this.inst_bin_code = (3'b101<<13) + (imm[11]<<12) + (imm[4]<<11) + (imm[9:8]<<9) + (imm[10]<<8) + (imm[6]<<7) + (imm[7]<<6) + (imm[3:1]<<3) + (imm[5]<<2) + 2'b01;  //offset
    end else if (this.inst_type == OP_C_BEQZ) begin
        this.inst_bin_code = (3'b110<<13) + (imm[8]<<12) + (imm[4:3]<<10) + (rs1[2:0]<<7) + (imm[7:6]<<5) + (imm[2:1]<<3) + (imm[5]<<2) + 2'b01;  //offset
    end else if (this.inst_type == OP_C_BNEZ) begin
        this.inst_bin_code = (3'b111<<13) + (imm[8]<<12) + (imm[4:3]<<10) + (rs1[2:0]<<7) + (imm[7:6]<<5) + (imm[2:1]<<3) + (imm[5]<<2) + 2'b01;  //offset
    end else if (this.inst_type == OP_C_SLLI) begin
        this.inst_bin_code = (3'b000<<13) + (imm[5]<<12) + (rd<<7) + (imm[4:0]<<2) + 2'b10;
//    end else if (this.inst_type == OP_C_SLLI64) begin
//        this.inst_bin_code = (3'b000<<13) + (1'b0<<12) + (rd<<7) + (5'b00000<<2) + 2'b10;
//DFP    end else if (this.inst_type == OP_C_FLDSP) begin
//DFP        this.inst_bin_code = (3'b001<<13) + (imm[5]<<12) + (rd<<7) + (imm[4:3]<<5) + (imm[8:6]<<2) + 2'b10;
//RV128    end else if (this.inst_type == OP_C_LQSP) begin
//RV128        this.inst_bin_code = (3'b001<<13) + (imm[5]<<12) + (rd<<7) + (imm[4]<<6) + (imm[9:6]<<2) + 2'b10;
    end else if (this.inst_type == OP_C_LWSP) begin
        this.inst_bin_code = (3'b010<<13) + (imm[5]<<12) + (rd<<7) + (imm[4:2]<<4) + (imm[7:6]<<2) + 2'b10;
//RV32    end else if (this.inst_type == OP_C_FLWSP) begin
//RV32        this.inst_bin_code = (3'b011<<13) + (imm[5]<<12) + (rd<<7) + (imm[4:2]<<4) + (imm[7:6]<<2) + 2'b10;
    end else if (this.inst_type == OP_C_LDSP) begin
        this.inst_bin_code = (3'b011<<13) + (imm[5]<<12) + (rd<<7) + (imm[4:3]<<5) + (imm[8:6]<<2) + 2'b10;
    end else if (this.inst_type == OP_C_JR) begin
        this.inst_bin_code = (3'b100<<13) + (1'b0<<12) + (rs1<<7) + (5'b00000<<2) + 2'b10;
    end else if (this.inst_type == OP_C_MV) begin
        this.inst_bin_code = (3'b100<<13) + (1'b0<<12) + (rd<<7) + (rs2<<2) + 2'b10;
    end else if (this.inst_type == OP_C_EBREAK) begin
        this.inst_bin_code = (3'b100<<13) + (1'b1<<12) + (5'b00000<<7) + (5'b00000<<2) + 2'b10;
    end else if (this.inst_type == OP_C_JALR) begin
        this.inst_bin_code = (3'b100<<13) + (1'b1<<12) + (rs1<<7) + (5'b00000<<2) + 2'b10;
    end else if (this.inst_type == OP_C_ADD) begin
        this.inst_bin_code = (3'b100<<13) + (1'b1<<12) + (rd<<7) + (rs2<<2) + 2'b10;
//DFP    end else if (this.inst_type == OP_C_FSDSP) begin
//DFP        this.inst_bin_code = (3'b101<<13) + (imm[5:3]<<10) + (imm[8:6]<<7) + (rs2<<2) + 2'b10;
//RV128    end else if (this.inst_type == OP_C_SQSP) begin
//RV128        this.inst_bin_code = (3'b101<<13) + (imm[5:4]<<11) + (imm[9:6]<<7) + (rs2<<2) + 2'b10;
    end else if (this.inst_type == OP_C_SWSP) begin
        this.inst_bin_code = (3'b110<<13) + (imm[5:2]<<9)  + (imm[7:6]<<7) + (rs2<<2) + 2'b10;
//RV32    end else if (this.inst_type == OP_C_FSWSP) begin
//RV32        this.inst_bin_code = (3'b111<<13) + (imm[5:2]<<9)  + (imm[7:6]<<7) + (rs2<<2) + 2'b10;
    end else if (this.inst_type == OP_C_SDSP) begin
        this.inst_bin_code = (3'b111<<13) + (imm[5:3]<<10) + (imm[8:6]<<7) + (rs2<<2) + 2'b10;
	end else begin
		`uvm_info("debug", $psprintf("Got an invalid instruction type 0x%0x\n", this.inst_type), UVM_HIGH);
        // TODO, randomly generate one illegal inst
        this.inst_bin_code = (25'b0 << 7) + 7'b1111111;
	end

    if (is_c_extension_inst(this.inst_bin_code)) begin
        inst_bin_code_size = 2;
    end
    else begin
        inst_bin_code_size = 4;
    end
endfunction: gen_inst_bin_code

function void riscv_inst_base_txn::inst_decode(bit[31:0] inst_code);
	this.is_rs1_valid = 0;
	this.is_rs2_valid = 0;
	this.is_rs3_valid = 0;
	this.is_rd_valid = 0;
    this.imm = 0;
    this.rm = 0;

    if ( is_c_extension_inst(inst_code) ) begin
        case (inst_code[1:0])
            2'b00: begin
                case (inst_code[15:13])
                    3'b000: begin
                        if (inst_code[12:2]==0) begin
                            this.inst_type = OP_C_ILLEGAL;
                        end
                        else begin
                            this.inst_type = OP_C_ADDI4SPN;     //z-ext
                            this.imm[9:6] = inst_code[10:7];
                            this.imm[5:4] = inst_code[12:11];
                            this.imm[3]   = inst_code[5];
                            this.imm[2]   = inst_code[6];
                            this.rd       = 8+inst_code[4:2];
                            this.is_rd_valid = 1;
                            this.rs1      = 2;
                            this.is_rs1_valid = 1;
                            if (imm==0) begin           
                                this.inst_type = OP_C_ILLEGAL;
                            end
                        end
                    end
                    3'b001: begin //C.FLD for double floating point, C.LQ for rv128
                        this.inst_type = OP_C_ILLEGAL;
                    end
                    3'b010: begin
                        this.inst_type = OP_C_LW;       //z-ext
                        this.imm[6]   = inst_code[5];
                        this.imm[5:3] = inst_code[12:10];
                        this.imm[2]   = inst_code[6];
                        this.rs1      = 8+inst_code[9:7];
                        this.rd       = 8+inst_code[4:2];
                        this.is_rs1_valid = 1;
                        this.is_rd_valid  = 1;
                    end
                    3'b011: begin
                        this.inst_type = OP_C_LD;       //z-ext
                        this.imm[7:6] = inst_code[6:5];
                        this.imm[5:3] = inst_code[12:10];
                        this.rs1      = 8+inst_code[9:7];
                        this.rd       = 8+inst_code[4:2];
                        this.is_rs1_valid = 1;
                        this.is_rd_valid  = 1;
                    end
                    3'b100: begin
                        this.inst_type = OP_C_ILLEGAL;  //RSVD
                    end
                    3'b101: begin //C.FSD for double floating point, C.SQ for rv128
                        this.inst_type = OP_C_ILLEGAL;
                    end
                    3'b110: begin
                        this.inst_type = OP_C_SW;       //z-ext
                        this.imm[2] = inst_code[6];
                        this.imm[6] = inst_code[5];
                        this.imm[5:3] = inst_code[12:10];
                        this.rs1      = 8+inst_code[9:7];
                        this.rs2      = 8+inst_code[4:2];
                        this.is_rs1_valid = 1;
                        this.is_rs2_valid = 1;
                    end
                    3'b111: begin
                        this.inst_type = OP_C_SD;       //z-ext
                        this.imm[7:6] = inst_code[6:5];
                        this.imm[5:3] = inst_code[12:10];
                        this.rs1      = 8+inst_code[9:7];
                        this.rs2      = 8+inst_code[4:2];
                        this.is_rs1_valid = 1;
                        this.is_rs2_valid = 1;
                    end
                endcase
            end
            2'b01: begin
                case (inst_code[15:13])
                    3'b000: begin
                        if (inst_code[12:2]==0) begin
                            this.inst_type = OP_C_NOP;
                        end
                        else begin
                            this.inst_type = OP_C_ADDI; //s-ext
                            this.imm[5]   = inst_code[12];
                            this.imm[4:0] = inst_code[6:2];
                            this.rd       = inst_code[11:7];
                            this.rs1      = inst_code[11:7];
                            this.is_rs1_valid = 1;
                            this.is_rd_valid = 1;
                            if (rd==0) begin
                                this.inst_type = OP_C_ILLEGAL;
                            end
                        end
                    end
                    3'b001: begin
                        this.inst_type = OP_C_ADDIW;    //s-ext
                        this.imm[5]   = inst_code[12];
                        this.imm[4:0] = inst_code[6:2];
                        this.rd       = inst_code[11:7];
                        this.rs1      = inst_code[11:7];
                        this.is_rs1_valid = 1;
                        this.is_rd_valid = 1;
                        if (rd==0) begin           
                            this.inst_type = OP_C_ILLEGAL;
                        end
                    end
                    3'b010: begin
                        this.inst_type = OP_C_LI;       //s-ext
                        this.imm[5]   = inst_code[12];
                        this.imm[4:0] = inst_code[6:2];
                        this.rd       = inst_code[11:7];
                        this.is_rd_valid = 1;
                    end
                    3'b011: begin
                        if (inst_code[11:7] == 2) begin
                            this.inst_type = OP_C_ADDI16SP; //s-ext
                            this.imm[9] = inst_code[12];
                            this.imm[8:7] = inst_code[4:3];
                            this.imm[6] = inst_code[5];
                            this.imm[5] = inst_code[2];
                            this.imm[4] = inst_code[6];
                            if (imm[9:4]==0) begin
                                this.inst_type = OP_C_ILLEGAL;
                            end
                            this.is_rs1_valid = 1;
                            this.rs1 = 2;
                            this.is_rd_valid = 1;
                            this.rd = 2;
                        end
                        else begin
                            this.inst_type = OP_C_LUI;      //s-ext
                            this.imm[17]    = inst_code[12];
                            this.imm[16:12] = inst_code[6:2];
                            this.rd         = inst_code[11:7];
                            this.is_rd_valid = 1;
//                            if (rd == 2) begin
//                                this.inst_type = OP_C_ILLEGAL;
//                            end
//                            else if (imm[17:12]==0) begin
                            if (imm[17:12]==0) begin
                                this.inst_type = OP_C_ILLEGAL;
                            end
                        end
                    end
                    3'b100: begin
                        case (inst_code[11:10])
                            2'b00: begin
                                this.inst_type = OP_C_SRLI;
                                this.imm[5]   = inst_code[12];
                                this.imm[4:0] = inst_code[6:2];
                                this.rd = 8+inst_code[9:7];
                                this.rs1 = 8+inst_code[9:7];
                                this.is_rs1_valid = 1;
                                this.is_rd_valid = 1;
                                if (imm[5:0]==0) begin
                                    this.inst_type = OP_C_ILLEGAL;
                                end
                            end
                            2'b01: begin
                                this.inst_type = OP_C_SRAI;
                                this.imm[5]   = inst_code[12];
                                this.imm[4:0] = inst_code[6:2];
                                this.rs1 = 8+inst_code[9:7];
                                this.rd = 8+inst_code[9:7];
                                this.is_rs1_valid = 1;
                                this.is_rd_valid = 1;
                                if (imm[5:0]==0) begin
                                    this.inst_type = OP_C_ILLEGAL;
                                end
                            end
                            2'b10: begin
                                this.inst_type = OP_C_ANDI;     //s-ext
                                this.imm[5] = inst_code[12];
                                this.imm[4:0] = inst_code[6:2];
                                this.rs1 = 8+inst_code[9:7];
                                this.rd  = 8+inst_code[9:7];
                                this.is_rs1_valid = 1;
                                this.is_rd_valid = 1;
                            end
                            2'b11: begin
                                this.rs1 = 8+inst_code[9:7];
                                this.rs2 = 8+inst_code[4:2];
                                this.rd  = 8+inst_code[9:7];
                                this.is_rs1_valid = 1;
                                this.is_rs2_valid = 1;
                                this.is_rd_valid = 1;
                                case ({inst_code[12], inst_code[6:5]})
                                    3'b000: this.inst_type = OP_C_SUB;
                                    3'b001: this.inst_type = OP_C_XOR;
                                    3'b010: this.inst_type = OP_C_OR;
                                    3'b011: this.inst_type = OP_C_AND;
                                    3'b100: this.inst_type = OP_C_SUBW;
                                    3'b101: this.inst_type = OP_C_ADDW;
                                    3'b110, 3'b111: this.inst_type = OP_C_ILLEGAL; //RSVD
                                endcase
                            end
                        endcase
                    end
                    3'b101: begin
                        this.inst_type = OP_C_J;    //s-ext
                        this.imm[11]  = inst_code[12];
                        this.imm[10]  = inst_code[8];
                        this.imm[9:8] = inst_code[10:9];
                        this.imm[7]   = inst_code[6];
                        this.imm[6]   = inst_code[7];
                        this.imm[5]   = inst_code[2];
                        this.imm[4]   = inst_code[11];
                        this.imm[3:1] = inst_code[5:3];
                        this.rd = 0;
                        this.is_rd_valid = 1;
                    end
                    3'b110: begin
                        this.inst_type = OP_C_BEQZ; //s-ext
                        this.imm[8]   = inst_code[12];
                        this.imm[7:6] = inst_code[6:5];
                        this.imm[5]   = inst_code[2];
                        this.imm[4:3] = inst_code[11:10];
                        this.imm[2:1] = inst_code[4:3];
                        this.rs1 = 8+inst_code[9:7];
                        this.is_rs1_valid = 1;
                        this.rs2 = 0;
                    end
                    3'b111: begin
                        this.inst_type = OP_C_BNEZ; //s-ext
                        this.imm[8]   = inst_code[12];
                        this.imm[7:6] = inst_code[6:5];
                        this.imm[5]   = inst_code[2];
                        this.imm[4:3] = inst_code[11:10];
                        this.imm[2:1] = inst_code[4:3];
                        this.rs1 = 8+inst_code[9:7];
                        this.is_rs1_valid = 1;
                        this.rs2 = 0;
                    end
                endcase
            end
            2'b10: begin
                case (inst_code[15:13])
                    3'b000: begin
                        this.inst_type = OP_C_SLLI;
                        this.imm[5]   = inst_code[12];
                        this.imm[4:0] = inst_code[6:2];
                        this.rd = inst_code[11:7];
                        this.rs1 = inst_code[11:7];
                        this.is_rd_valid = 1;
                        this.is_rs1_valid = 1;
                        if (imm[5:0] == 0) begin
                            this.inst_type = OP_C_ILLEGAL;
                        end
                    end
                    3'b001: begin //C.FLDSP for double floating point, C.LQSP for rv128
                        this.inst_type = OP_C_ILLEGAL;
                    end
                    3'b010: begin
                        this.inst_type = OP_C_LWSP; //z-ext
                        this.imm[7:6] = inst_code[3:2];
                        this.imm[5] = inst_code[12];
                        this.imm[4:2] = inst_code[6:4];
                        this.rs1 = 2;
                        this.is_rs1_valid = 1;
                        this.rd = inst_code[11:7];
                        this.is_rd_valid = 1;
                        if (rd==0) begin
                            this.inst_type = OP_C_ILLEGAL;
                        end
                    end
                    3'b011: begin
                        this.inst_type = OP_C_LDSP; //z-ext
                        this.imm[8:6] = inst_code[4:2];
                        this.imm[5] = inst_code[12];
                        this.imm[4:3] = inst_code[6:5];
                        this.rs1 = 2;
                        this.is_rs1_valid = 1;
                        this.rd = inst_code[11:7];
                        this.is_rd_valid = 1;
                        if (rd==0) begin
                            this.inst_type = OP_C_ILLEGAL;
                        end
                    end
                    3'b100: begin
                        case (inst_code[12])
                            1'b0: begin
                                if (inst_code[6:2] == 0) begin
                                    begin
                                        this.inst_type = OP_C_JR; 
                                        this.rs1 = inst_code[11:7];
                                        this.rd = 0;
                                        this.is_rs1_valid = 1;
                                        this.is_rd_valid = 1;
                                        if (inst_code[11:7] == 0) begin
                                            this.inst_type = OP_C_ILLEGAL;
                                        end
                                    end
                                end
                                else begin //inst_code[6:2] != 0
                                    this.inst_type = OP_C_MV;
                                    this.rd  = inst_code[11:7];
                                    this.rs1 = 0;
                                    this.rs2 = inst_code[6:2];
                                    this.is_rs1_valid = 1;
                                    this.is_rs2_valid = 1;
                                    this.is_rd_valid = 1;
                                end
                            end
                            1'b1: begin //inst_code[12]
                                if (inst_code[6:2] == 0) begin
                                    if (inst_code[11:7] == 0) begin
                                        this.inst_type = OP_C_EBREAK;
                                    end
                                    else begin
                                        this.inst_type = OP_C_JALR;
                                        this.rs1 = inst_code[11:7];
                                        this.rd = 1;
                                        this.is_rs1_valid = 1;
                                        this.is_rd_valid = 1;
                                    end
                                end
                                else begin //inst_code[6:2] != 0
                                    this.inst_type = OP_C_ADD;
                                    this.rd  = inst_code[11:7];
                                    this.rs1 = inst_code[11:7];
                                    this.rs2 = inst_code[6:2];
                                    this.is_rs1_valid = 1;
                                    this.is_rs2_valid = 1;
                                    this.is_rd_valid = 1;
                                end
                            end
                        endcase
                    end
                    3'b101: begin //C.FSDSP for double floating point, C.SQSP for rv128
                        this.inst_type = OP_C_ILLEGAL;
                    end
                    3'b110: begin
                        this.inst_type = OP_C_SWSP;   //z-ext
                        this.imm[7:6] = inst_code[8:7];
                        this.imm[5:2] = inst_code[12:9];
                        this.rs1 = 2;
                        this.is_rs1_valid = 1;
                        this.rs2 = inst_code[6:2];
                        this.is_rs2_valid = 1;
                    end
                    3'b111: begin
                        this.inst_type = OP_C_SDSP;   //z-ext
                        this.imm[8:6] = inst_code[9:7];
                        this.imm[5:3] = inst_code[12:10];
                        this.rs1 = 2;
                        this.is_rs1_valid = 1;
                        this.rs2 = inst_code[6:2];
                        this.is_rs2_valid = 1;
                    end
                endcase
            end
        endcase
    end  //CEXT END
    else if (inst_code[6:0] == 7'b0110111) begin
        this.inst_type = OP_LUI;
        this.rd = inst_code[11:7];
        this.imm = {inst_code[31:12], 12'b0};
        this.is_rd_valid = 1;
    end
    else if (inst_code[6:0] == 7'b0010111) begin
        this.inst_type = OP_AUIPC;
        this.rd = inst_code[11:7];
        this.imm = {inst_code[31:12], 12'b0};
		this.is_rd_valid = 1;
    end
    else if (inst_code[6:0] == 7'b1101111) begin
        this.inst_type = OP_JAL;
        this.rd = inst_code[11:7];
        this.imm = 0;
        this.imm[20] = inst_code[31];
        this.imm[10:1] = inst_code[30:21];
        this.imm[11] = inst_code[20];
        this.imm[19:12] = inst_code[19:12];
		this.is_rd_valid = 1;
    end
    else if (inst_code[6:0] == 7'b1100111) begin
        if (inst_code[14:12] == 3'b000) begin
            this.inst_type = OP_JALR;
            this.rd = inst_code[11:7];
            this.rs1 = inst_code[19:15];
            this.imm = inst_code[31:20];
			this.is_rd_valid = 1;
			this.is_rs1_valid = 1;
        end
        else begin
            this.inst_type = OP_ILLEGAL;
        end
    end
    else if (inst_code[6:0] == 7'b1100011) begin
        if (inst_code[14:12] == 3'b000) begin
            this.inst_type = OP_BEQ;
        end
        else if (inst_code[14:12] == 3'b001) begin
            this.inst_type = OP_BNE;
        end
        else if (inst_code[14:12] == 3'b100) begin
            this.inst_type = OP_BLT;
        end
        else if (inst_code[14:12] == 3'b101) begin
            this.inst_type = OP_BGE;
        end
        else if (inst_code[14:12] == 3'b110) begin
            this.inst_type = OP_BLTU;
        end
        else if (inst_code[14:12] == 3'b111) begin
            this.inst_type = OP_BGEU;
        end
        else begin
            this.inst_type = OP_ILLEGAL;
        end

        this.rs1 = inst_code[19:15];
        this.rs2 = inst_code[24:20];
        this.imm = 0;
        this.imm[12] = inst_code[31];
        this.imm[10:5] = inst_code[30:25];
        this.imm[4:1] = inst_code[11:8];
        this.imm[11] = inst_code[7];
		this.is_rs1_valid = 1;
		this.is_rs2_valid = 1;
    end
    else if (inst_code[6:0] == 7'b0000011) begin
        if (inst_code[14:12] == 3'b000) begin
            this.inst_type = OP_LB;
        end
        else if (inst_code[14:12] == 3'b001) begin
            this.inst_type = OP_LH;
        end
        else if (inst_code[14:12] == 3'b010) begin
            this.inst_type = OP_LW;
        end
        else if (inst_code[14:12] == 3'b100) begin
            this.inst_type = OP_LBU;
        end
        else if (inst_code[14:12] == 3'b101) begin
            this.inst_type = OP_LHU;
        end
        else if (inst_code[14:12] == 3'b110) begin
            this.inst_type = OP_LWU;
        end
        else if (inst_code[14:12] == 3'b011) begin
            this.inst_type = OP_LD;
        end
        else begin
            this.inst_type = OP_ILLEGAL;
        end
        
        this.rd = inst_code[11:7];
        this.rs1 = inst_code[19:15];
        this.imm = inst_code[31:20];
		this.is_rs1_valid = 1;
		this.is_rd_valid = 1;
    end
    else if (inst_code[6:0] == 7'b0100011) begin
        if (inst_code[14:12] == 3'b000) begin
            this.inst_type = OP_SB;
        end
        else if (inst_code[14:12] == 3'b001) begin
            this.inst_type = OP_SH;
        end
        else if (inst_code[14:12] == 3'b010) begin
            this.inst_type = OP_SW;
        end
        else if (inst_code[14:12] == 3'b011) begin
            this.inst_type = OP_SD;
        end
        else begin
            this.inst_type = OP_ILLEGAL;
        end
        
        this.rs1 = inst_code[19:15];
        this.rs2 = inst_code[24:20];
        this.imm[11:5] = inst_code[31:25];
        this.imm[4:0] = inst_code[11:7];
		this.is_rs1_valid = 1;
		this.is_rs2_valid = 1;
    end
    else if (inst_code[6:0] == 7'b0010011) begin
        this.rd = inst_code[11:7];
        this.rs1 = inst_code[19:15];
        this.imm = inst_code[31:20];
		this.is_rs1_valid = 1;
		this.is_rd_valid = 1;
        
        if (inst_code[14:12] == 3'b000) begin
            this.inst_type = OP_ADDI;
        end
        else if (inst_code[14:12] == 3'b001) begin
            if (inst_code[31:26] == 6'b000000) begin
                this.inst_type = OP_SLLI;
                this.imm = 0;
                this.imm[5:0] = inst_code[25:20];
            end
            else begin
                this.inst_type = OP_ILLEGAL;
            end
        end
        else if (inst_code[14:12] == 3'b010) begin
            this.inst_type = OP_SLTI;
        end
        else if (inst_code[14:12] == 3'b011) begin
            this.inst_type = OP_SLTIU;
        end
        else if (inst_code[14:12] == 3'b100) begin
            this.inst_type = OP_XORI;
        end
        else if (inst_code[14:12] == 3'b101) begin
            if (inst_code[31:26] == 6'b000000) begin
                this.inst_type = OP_SRLI;
                this.imm = 0;
                this.imm[5:0] = inst_code[25:20];
            end
            else if (inst_code[31:26] == 6'b010000) begin
                this.inst_type = OP_SRAI;
                this.imm = 0;
                this.imm[5:0] = inst_code[25:20];
            end
            else begin
                this.inst_type = OP_ILLEGAL;
            end
        end
        else if (inst_code[14:12] == 3'b110) begin
            this.inst_type = OP_ORI;
        end
        else if (inst_code[14:12] == 3'b111) begin
            this.inst_type = OP_ANDI;
        end
        else begin
            this.inst_type = OP_ILLEGAL;
        end
    end
    else if (inst_code[6:0] == 7'b0110011) begin
        if (inst_code[14:12] == 3'b000) begin
            if (inst_code[31:25] == 7'b0000000) begin
                this.inst_type = OP_ADD;
            end
            else if (inst_code[31:25] == 7'b0100000) begin
                this.inst_type = OP_SUB;
            end
            else if (inst_code[31:25] == 7'b0000001) begin
                this.inst_type = OP_MUL;
            end
            else begin
                this.inst_type = OP_ILLEGAL;
            end
        end
        else if (inst_code[14:12] == 3'b001) begin
            if (inst_code[31:25] == 7'b0000000) begin
                this.inst_type = OP_SLL;
            end
            else if (inst_code[31:25] == 7'b0000001) begin
                this.inst_type = OP_MULH;
            end
            else begin
                this.inst_type = OP_ILLEGAL;
            end
        end
        else if (inst_code[14:12] == 3'b010) begin
            if (inst_code[31:25] == 7'b0000000) begin
                this.inst_type = OP_SLT;
            end
            else if (inst_code[31:25] == 7'b0000001) begin
                this.inst_type = OP_MULHSU;
            end
            else begin
                this.inst_type = OP_ILLEGAL;
            end
        end
        else if (inst_code[14:12] == 3'b011) begin
            if (inst_code[31:25] == 7'b0000000) begin
                this.inst_type = OP_SLTU;
            end
            else if (inst_code[31:25] == 7'b0000001) begin
                this.inst_type = OP_MULHU;
            end
            else begin
                this.inst_type = OP_ILLEGAL;
            end
        end
        else if (inst_code[14:12] == 3'b100) begin
            if (inst_code[31:25] == 7'b0000000) begin
                this.inst_type = OP_XOR;
            end
            else if (inst_code[31:25] == 7'b0000001) begin
                this.inst_type = OP_DIV;
            end
            else begin
                this.inst_type = OP_ILLEGAL;
            end
        end
        else if (inst_code[14:12] == 3'b101) begin
            if (inst_code[31:25] == 7'b0000000) begin
                this.inst_type = OP_SRL;
            end
            else if (inst_code[31:25] == 7'b0100000) begin
                this.inst_type = OP_SRA;
            end
            else if (inst_code[31:25] == 7'b0000001) begin
                this.inst_type = OP_DIVU;
            end
            else begin
                this.inst_type = OP_ILLEGAL;
            end
        end
        else if (inst_code[14:12] == 3'b110) begin
            if (inst_code[31:25] == 7'b0000000) begin
                this.inst_type = OP_OR;
            end
            else if (inst_code[31:25] == 7'b0000001) begin
                this.inst_type = OP_REM;
            end
            else begin
                this.inst_type = OP_ILLEGAL;
            end
        end
        else if (inst_code[14:12] == 3'b111) begin
            if (inst_code[31:25] == 7'b0000000) begin
                this.inst_type = OP_AND;
            end
            else if (inst_code[31:25] == 7'b0000001) begin
                this.inst_type = OP_REMU;
            end
            else begin
                this.inst_type = OP_ILLEGAL;
            end
        end
        else begin
            this.inst_type = OP_ILLEGAL;
        end
        
        this.rd = inst_code[11:7];
        this.rs1 = inst_code[19:15];
        this.rs2 = inst_code[24:20];
		this.is_rs1_valid = 1;
		this.is_rs2_valid = 1;
		this.is_rd_valid = 1;
    end
    else if (inst_code[6:0] == 7'b0001111) begin
        if (inst_code[14:12] == 3'b000) begin
            if (inst_code[31:28] == 4'b0 && inst_code[19:15] == 5'b0 && inst_code[11:7] == 5'b0) begin
                this.inst_type = OP_FENCE;
                this.pred = inst_code[27:24];
                this.succ = inst_code[23:20];
                this.imm[7:4] = inst_code[27:24];
                this.imm[3:0] = inst_code[23:20];
            end
            else begin
                this.inst_type = OP_ILLEGAL;
            end
        end
        else if (inst_code[14:12] == 3'b001) begin
            if (inst_code[31:15] == 17'b0 && inst_code[11:7] == 5'b0) begin
                this.inst_type = OP_FENCEI;
            end
            else begin
                this.inst_type = OP_ILLEGAL;
            end
        end
        else begin
            this.inst_type = OP_ILLEGAL;
        end
    end
    else if (inst_code[6:0] == 7'b1110011) begin
        if (inst_code[14:12] == 3'b000) begin
            if (inst_code[31:20] == 12'b000000000000) begin
                if (inst_code[19:15] == 5'b0 && inst_code[11:7] == 5'b0) begin
                    this.inst_type = OP_ECALL;
                end
                else begin
                    this.inst_type = OP_ILLEGAL;
                end
            end
            else if (inst_code[31:20] == 12'b000000000001) begin
                if (inst_code[19:15] == 5'b0 && inst_code[11:7] == 5'b0) begin
                    this.inst_type = OP_EBREAK;
                end
                else begin
                    this.inst_type = OP_ILLEGAL;
                end
            end
            else if (inst_code[31:20] == 12'b001100000010) begin
                if (inst_code[19:15] == 5'b0 && inst_code[11:7] == 5'b0) begin
                    this.inst_type = OP_MRET;
                end
                else begin
                    this.inst_type = OP_ILLEGAL;
                end
            end
            else if (inst_code[31:20] == 12'b000100000010) begin
                if (inst_code[19:15] == 5'b0 && inst_code[11:7] == 5'b0) begin
                    this.inst_type = OP_SRET;
                end
                else begin
                    this.inst_type = OP_ILLEGAL;
                end
            end
            else if (inst_code[31:20] == 12'b000100000101) begin
                if (inst_code[19:15] == 5'b0 && inst_code[11:7] == 5'b0) begin
                    this.inst_type = OP_WFI;
                end
                else begin
                    this.inst_type = OP_ILLEGAL;
                end
            end
            else if (inst_code[31:25] == 7'b0001001) begin
                if (inst_code[11:7] == 5'b0) begin
                    this.inst_type = OP_SFENCE;
                end
                else begin
                    this.inst_type = OP_ILLEGAL;
                end
            end
            else begin
                this.inst_type = OP_ILLEGAL;
            end
        end
        else if (inst_code[14:12] == 3'b001) begin
            this.inst_type = OP_CSRRW;
            this.rd = inst_code[11:7];
            this.rs1 = inst_code[19:15];
            this.csr = inst_code[31:20];
            this.imm[16:5] = inst_code[31:20];
			this.is_rd_valid = 1;
			this.is_rs1_valid = 1;
        end
        else if (inst_code[14:12] == 3'b010) begin
            this.inst_type = OP_CSRRS;
            this.rd = inst_code[11:7];
            this.rs1 = inst_code[19:15];
            this.csr = inst_code[31:20];
            this.imm[16:5] = inst_code[31:20];
			this.is_rd_valid = 1;
			this.is_rs1_valid = 1;
        end
        else if (inst_code[14:12] == 3'b011) begin
            this.inst_type = OP_CSRRC;
            this.rd = inst_code[11:7];
            this.rs1 = inst_code[19:15];
            this.csr = inst_code[31:20];
            this.imm[16:5] = inst_code[31:20];
			this.is_rd_valid = 1;
			this.is_rs1_valid = 1;
        end
        else if (inst_code[14:12] == 3'b101) begin
            this.inst_type = OP_CSRRWI;
            this.rd = inst_code[11:7];
            this.imm[4:0] = inst_code[19:15];
            this.csr = inst_code[31:20];
            this.imm[16:5] = inst_code[31:20];
			this.is_rd_valid = 1;
        end
        else if (inst_code[14:12] == 3'b110) begin
            this.inst_type = OP_CSRRSI;
            this.rd = inst_code[11:7];
            this.imm[4:0] = inst_code[19:15];
            this.csr = inst_code[31:20];
            this.imm[16:5] = inst_code[31:20];
			this.is_rd_valid = 1;
        end
        else if (inst_code[14:12] == 3'b111) begin
            this.inst_type = OP_CSRRCI;
            this.rd = inst_code[11:7];
            this.imm[4:0] = inst_code[19:15];
            this.csr = inst_code[31:20];
            this.imm[16:5] = inst_code[31:20];
			this.is_rd_valid = 1;
        end
        else begin
            this.inst_type = OP_ILLEGAL;
        end
    end
    else if (inst_code[6:0] == 7'b0011011) begin
        this.rd = inst_code[11:7];
        this.rs1 = inst_code[19:15];
		this.is_rd_valid = 1;
		this.is_rs1_valid = 1;
        
        if (inst_code[14:12] == 3'b000) begin
            this.inst_type = OP_ADDIW;
            this.imm = inst_code[31:20];
        end
        else if (inst_code[14:12] == 3'b001) begin
            if (inst_code[31:25] == 7'b0000000) begin
                this.inst_type = OP_SLLIW;
                this.imm = 0;
                this.imm[4:0] = inst_code[24:20];
            end
            else begin
                this.inst_type = OP_ILLEGAL;
            end
        end
        else if (inst_code[14:12] == 3'b101) begin
            if (inst_code[31:25] == 7'b0000000) begin
                this.inst_type = OP_SRLIW;
                this.imm = 0;
                this.imm[4:0] = inst_code[24:20];
            end
            else if (inst_code[31:25] == 7'b0100000) begin
                this.inst_type = OP_SRAIW;
                this.imm = 0;
                this.imm[4:0] = inst_code[24:20];
            end
            else begin
                this.inst_type = OP_ILLEGAL;
            end
        end
        else begin
            this.inst_type = OP_ILLEGAL;
        end
    end
    else if (inst_code[6:0] == 7'b0111011) begin
        if (inst_code[14:12] == 3'b000) begin
            if (inst_code[31:25] == 7'b0000000) begin
                this.inst_type = OP_ADDW;
            end
            else if (inst_code[31:25] == 7'b0100000) begin
                this.inst_type = OP_SUBW;
            end
            else if (inst_code[31:25] == 7'b0000001) begin
                this.inst_type = OP_MULW;
            end
            else begin
                this.inst_type = OP_ILLEGAL;
            end
        end
        else if (inst_code[14:12] == 3'b001) begin
            if (inst_code[31:25] == 7'b0000000) begin
                this.inst_type = OP_SLLW;
            end
            else begin
                this.inst_type = OP_ILLEGAL;
            end
        end
        else if (inst_code[14:12] == 3'b100) begin
            if (inst_code[31:25] == 7'b0000001) begin
                this.inst_type = OP_DIVW;
            end
            else begin
                this.inst_type = OP_ILLEGAL;
            end
        end
        else if (inst_code[14:12] == 3'b101) begin
            if (inst_code[31:25] == 7'b0000000) begin
                this.inst_type = OP_SRLW;
            end
            else if (inst_code[31:25] == 7'b0100000) begin
                this.inst_type = OP_SRAW;
            end
            else if (inst_code[31:25] == 7'b0000001) begin
                this.inst_type = OP_DIVUW;
            end
            else begin
                this.inst_type = OP_ILLEGAL;
            end
        end
        else if (inst_code[14:12] == 3'b110) begin
            if (inst_code[31:25] == 7'b0000001) begin
                this.inst_type = OP_REMW;
            end
            else begin
                this.inst_type = OP_ILLEGAL;
            end
        end
        else if (inst_code[14:12] == 3'b111) begin
            if (inst_code[31:25] == 7'b0000001) begin
                this.inst_type = OP_REMUW;
            end
            else begin
                this.inst_type = OP_ILLEGAL;
            end
        end
        else begin
            this.inst_type = OP_ILLEGAL;
        end
        
        this.rd  = inst_code[11:7];
        this.rs1 = inst_code[19:15];
        this.rs2 = inst_code[24:20];
		this.is_rd_valid  = 1;
		this.is_rs1_valid = 1;
		this.is_rs2_valid = 1;
    end else if (inst_code[6:0] == 7'b000_0111) begin
        this.imm[11:0] = inst_code[31:20];
        this.rd  = inst_code[11:7];
        this.rs1 = inst_code[19:15];
        this.is_rd_valid  = 1;
        this.is_rs1_valid = 1;
        this.inst_type = OP_FLW;
    end else if (inst_code[6:0] == 7'b010_0111) begin
        this.imm[4:0] = inst_code[11:7];
        this.imm[11:5] = inst_code[31:25];
        this.rs1 = inst_code[19:15];
        this.rs2 = inst_code[24:20];
        this.is_rs1_valid = 1;
        this.is_rs2_valid = 1;
        this.inst_type = OP_FSW;
    end else if (inst_code[6:0] == 7'b100_0011) begin
        this.rs1 = inst_code[19:15];
        this.rs2 = inst_code[24:20];
        this.rs3 = inst_code[31:27];
        this.rd  = inst_code[11:7];
        this.rm  = inst_code[14:12];
        this.is_rs1_valid = 1;
        this.is_rs2_valid = 1;
        this.is_rs3_valid = 1;
        this.is_rd_valid  = 1;
        this.inst_type = OP_FMADD_S;
    end else if (inst_code[6:0] == 7'b100_0111) begin
        this.rs1 = inst_code[19:15];
        this.rs2 = inst_code[24:20];
        this.rs3 = inst_code[31:27];
        this.rd  = inst_code[11:7];
        this.rm  = inst_code[14:12];
        this.is_rs1_valid = 1;
        this.is_rs2_valid = 1;
        this.is_rs3_valid = 1;
        this.is_rd_valid  = 1;
        this.inst_type = OP_FMSUB_S;
    end else if (inst_code[6:0] == 7'b100_1111) begin
        this.rs1 = inst_code[19:15];
        this.rs2 = inst_code[24:20];
        this.rs3 = inst_code[31:27];
        this.rd  = inst_code[11:7];
        this.rm  = inst_code[14:12];
        this.is_rs1_valid = 1;
        this.is_rs2_valid = 1;
        this.is_rs3_valid = 1;
        this.is_rd_valid  = 1;
        this.inst_type = OP_FNMADD_S;
    end else if (inst_code[6:0] == 7'b100_1011) begin
        this.rs1 = inst_code[19:15];
        this.rs2 = inst_code[24:20];
        this.rs3 = inst_code[31:27];
        this.rd  = inst_code[11:7];
        this.rm  = inst_code[14:12];
        this.is_rs1_valid = 1;
        this.is_rs2_valid = 1;
        this.is_rs3_valid = 1;
        this.is_rd_valid  = 1;
        this.inst_type = OP_FNMSUB_S;
    end else if (inst_code[6:0] == 7'b101_0011) begin
        this.rd  = inst_code[11:7];
        this.rs1 = inst_code[19:15];
        this.rs2 = inst_code[24:20];
        this.is_rd_valid  = 1;
        this.is_rs1_valid = 1;
        this.is_rs2_valid = 1;
        if (inst_code[31:25] == 7'b000_0000) begin
            this.inst_type = OP_FADD_S;
            this.rm  = inst_code[14:12];
        end else if (inst_code[31:25] == 7'b000_0100) begin
            this.inst_type = OP_FSUB_S;
            this.rm  = inst_code[14:12];
        end else if (inst_code[31:25] == 7'b000_1000) begin
            this.inst_type = OP_FMUL_S;
            this.rm  = inst_code[14:12];
        end else if (inst_code[31:25] == 7'b000_1100) begin
            this.inst_type = OP_FDIV_S;
            this.rm  = inst_code[14:12];
        end else if (inst_code[31:25] == 7'b010_1100) begin
            this.inst_type = OP_FSQRT_S;
            this.rm  = inst_code[14:12];
            this.is_rs2_valid = 0;
        end else if (inst_code[31:25] == 7'b001_0000) begin
          if (inst_code[14:12] == 3'b000) begin
            this.inst_type = OP_FSGNJ_S;
          end else if (inst_code[14:12] == 3'b001) begin
            this.inst_type = OP_FSGNJN_S;
          end else if (inst_code[14:12] == 3'b010) begin
            this.inst_type = OP_FSGNJX_S;
          end else begin
            this.inst_type = OP_ILLEGAL;
          end
        end else if (inst_code[31:25] == 7'b001_0100) begin
          if (inst_code[14:12] == 3'b000) begin
            this.inst_type = OP_FMIN_S;
          end else if (inst_code[14:12] == 3'b001) begin
            this.inst_type = OP_FMAX_S;
          end else begin
            this.inst_type = OP_ILLEGAL;
          end
        end else if (inst_code[31:25] == 7'b111_0000) begin
          if (inst_code[14:12] == 3'b000) begin
            this.inst_type = OP_FMV_X_S;
            this.is_rs2_valid = 0;
          end else if (inst_code[14:12] == 3'b001) begin
            this.inst_type = OP_FCLASS_S;
            this.is_rs2_valid = 0;
          end else begin
            this.inst_type = OP_ILLEGAL;
          end
        end else if (inst_code[31:25] == 7'b111_1000) begin
            this.inst_type = OP_FMV_S_X;
            this.is_rs2_valid = 0;
        end else if (inst_code[31:25] == 7'b101_0000) begin
          if (inst_code[14:12] == 3'b010) begin
            this.inst_type = OP_FEQ_S;
          end else if (inst_code[14:12] == 3'b001) begin
            this.inst_type = OP_FLT_S;
          end else if (inst_code[14:12] == 3'b000) begin
            this.inst_type = OP_FLE_S;
          end else begin
            this.inst_type = OP_ILLEGAL;
          end
        end else if (inst_code[31:25] == 7'b110_0000) begin
          this.is_rs2_valid = 0;
          if (inst_code[24:20] == 5'b0_0000) begin
            this.inst_type = OP_FCVT_W_S;
            this.rm  = inst_code[14:12];
          end else if (inst_code[24:20] == 5'b0_0001) begin
            this.inst_type = OP_FCVT_WU_S;
            this.rm  = inst_code[14:12];
          end else if (inst_code[24:20] == 5'b0_0010) begin
            this.inst_type = OP_FCVT_L_S;
            this.rm  = inst_code[14:12];
          end else if (inst_code[24:20] == 5'b0_0011) begin
            this.inst_type = OP_FCVT_LU_S;
            this.rm  = inst_code[14:12];
          end else begin
            this.inst_type = OP_ILLEGAL;
          end
        end else if (inst_code[31:25] == 7'b110_1000) begin
          this.is_rs2_valid = 0;
          if (inst_code[24:20] == 5'b0_0000) begin
            this.inst_type = OP_FCVT_S_W;
            this.rm  = inst_code[14:12];
          end else if (inst_code[24:20] == 5'b0_0001) begin
            this.inst_type = OP_FCVT_S_WU;
            this.rm  = inst_code[14:12];
          end else if (inst_code[24:20] == 5'b0_0010) begin
            this.inst_type = OP_FCVT_S_L;
            this.rm  = inst_code[14:12];
          end else if (inst_code[24:20] == 5'b0_0011) begin
            this.inst_type = OP_FCVT_S_LU;
            this.rm  = inst_code[14:12];
          end else begin
            this.inst_type = OP_ILLEGAL;
          end
        end else begin
            this.inst_type = OP_ILLEGAL;
        end
    end else begin
        this.inst_type = OP_ILLEGAL;
    end
endfunction

function bit riscv_inst_base_txn::is_c_extension_inst(bit[31:0] inst_code);
    if (inst_code[1:0] != 2'b11) begin
        is_rvc_inst = 1;
    end
    else begin
        is_rvc_inst = 0;
    end

    return is_rvc_inst;
endfunction

`endif // RISCV_INST_BASE_TXN__SV
