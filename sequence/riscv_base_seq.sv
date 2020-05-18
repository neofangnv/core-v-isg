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

`ifndef RISCV_BASE_SEQ__SV
`define RISCV_BASE_SEQ__SV

import uvm_pkg::*;
import riscv_txn_pkg::*;
import riscv_memory_pkg::*;
`include "riscv_params.sv"

class rand_gpr extends uvm_sequence_item;
  rand bit [63:0] gpr[31];

  `uvm_object_utils_begin(rand_gpr)
    `uvm_field_sarray_int(gpr, UVM_ALL_ON)
  `uvm_object_utils_end

  constraint c_gpr {
    foreach (gpr[i]) gpr[i] dist {0 := 1, [1:'hffff_fffe] :/ 10, 'hffff_ffff :/1, ['h1_0000_0000:'hffff_fffe_ffff_ffff] :/ 20, 'hffff_ffff_0000_0000 :/ 1, ['hffff_ffff_0000_0001:'hffff_ffff_ffff_fffe] :/ 10, 'hffff_ffff_ffff_ffff :/ 1};
  }

  function new (string name = "rand_gpr");
    super.new(name);
  endfunction

  // override do_print to customize how to print/sprint
  virtual function void do_print(uvm_printer printer);
    super.do_print(printer);

    // to be able to print all elements of an array
    printer.knobs.begin_elements = -1;
    printer.knobs.end_elements = -1;
  endfunction
endclass

class rand_txn extends uvm_sequence_item;
  rand bit [63:0] value;

  `uvm_object_utils_begin(rand_txn)
    `uvm_field_int(value, UVM_ALL_ON)
  `uvm_object_utils_end

  function new (string name = "rand_txn");
    super.new(name);
  endfunction
endclass

class pmpaddr_cfg extends uvm_sequence_item;
    rand bit [63:0] paddr                                      ;
    rand bit [63:0] min_addr                                   ;
    rand bit [63:0] max_addr                                   ;
    rand bit [64:0] range                                      ;
    bit full_range;


    `uvm_object_utils_begin(pmpaddr_cfg)
    `uvm_field_int(paddr     , UVM_ALL_ON)
    `uvm_field_int(min_addr , UVM_ALL_ON)
    `uvm_field_int(max_addr , UVM_ALL_ON)
  `uvm_object_utils_end

  function new (string name = "pmpaddr_cfg");
    super.new(name);
    paddr      =  0;
    min_addr  =  0;
    max_addr  =  0;
        full_range = 0;
        range     = 0;
  endfunction

    function void cal_addr(int cfg_mode);
        //the min range of a pmp entry is 1KB.
        bit[63:0] tmp;
        int    i;
        min_addr[1:0] = 'h0;
        max_addr[1:0] = 'h0;
        if(cfg_mode == `PMP_TOR) begin
            paddr = (max_addr>>2);
            range = max_addr - min_addr;
            //the previous paddr = min_addr
        end
        else if(cfg_mode == `PMP_NA4) begin
            //4byte range
            paddr    = (min_addr>>2);
            max_addr = min_addr + 4;
            range    = 4;
        end
        else begin  //NAPOT mode, >= 8bytes
            if(full_range == 0)begin
                tmp = (max_addr - min_addr);

                for(i=3; i<64; i++) begin
                    if(tmp == (1<<i)) begin
                        min_addr = (min_addr>>i)<<i;
                        break;
                    end
                    else if((tmp > (1<<i)) && (tmp < (1<<(i+1)))) begin
                        i = i+1;
                        min_addr = (min_addr>>i)<<i;
                        break;
                    end
                end
                `uvm_info("init_pmp_cfg", $psprintf("cal_addr,i=0x%x", i), UVM_HIGH)
                if((min_addr + (1<<i)) < max_addr) begin
                    i = i+1;
                    min_addr = (min_addr>>i)<<i;
                end
                `uvm_info("init_pmp_cfg", $psprintf("cal_addr,i=0x%x", i), UVM_HIGH)

                if(i==64)begin
                    paddr = 64'h1fff_ffff_ffff_ffff;
                    min_addr = 'h0;
                    range = 65'h1_0000_0000_0000_0000;
                end
                else begin
                    paddr  = min_addr>>2;
                    tmp   = (1<<(i-3)) -1;
                    paddr  = paddr | tmp;
                    range = (1<<i);
                end
            end
            else begin
                paddr = 64'h1fff_ffff_ffff_ffff;
                min_addr = 'h0;
                range = 65'h1_0000_0000_0000_0000;
            end
        end
        `uvm_info("debug", $psprintf("setup a core pmp entry. min_addr = 0x%16x, range = 0x%0x, paddr=0x%16x", min_addr, range, paddr), UVM_HIGH);
    endfunction
    function int is_in_entry_range(bit[63:0] addr);
        return (addr>= min_addr) && (addr < (min_addr + range));
    endfunction
endclass

class pmpcfg_cfg extends uvm_sequence_item;
    rand bit      r;
    rand bit      w;
    rand bit      x;
    rand bit[1:0] a;
    rand bit[1:0] s;
    rand bit      l;
    bit[7:0]      value;

    `uvm_object_utils_begin(pmpcfg_cfg)
    `uvm_field_int(r, UVM_ALL_ON)
    `uvm_field_int(w, UVM_ALL_ON)
    `uvm_field_int(x, UVM_ALL_ON)
    `uvm_field_int(a, UVM_ALL_ON)
    `uvm_field_int(s, UVM_ALL_ON)
    `uvm_field_int(l, UVM_ALL_ON)
  `uvm_object_utils_end

  function new (string name = "pmpaddr_cfg");
    super.new(name);
        a = 0       ;
    r = $urandom;
    w = $urandom;
    x = $urandom;
    s = $urandom;
    l = 0       ;
  endfunction
    function bit[7:0] pack_cfg();
        value = {l,s, a, x, w, r};
        return value;
    endfunction
endclass

class csr_field extends uvm_sequence_item;
    bit [63:0] field_value;
    int idx_high;
    int idx_low;
    bit [63:0] field_mask;
    string attr;

    bit illegal_value_arr [*];
    bit ignore_value_arr [*];

  function new (string name = "csr_field");
    super.new(name);
  endfunction

    function void get_field_mask();
        field_mask = 0;

        for (int i=0; i<=(idx_high-idx_low); i++) begin
            field_mask += 1 << i;
        end
    endfunction

    function bit is_illegal_value();
        if (illegal_value_arr.exists(field_value)) begin
            return 1;
        end
        else begin
            return 0;
        end
    endfunction

    function bit is_ignore_value();
        if (ignore_value_arr.exists(field_value)) begin
            return 1;
        end
        else begin
            return 0;
        end
    endfunction
endclass

class csr_register extends uvm_sequence_item;
    csr_field field_queue[$];
    bit [63:0] reg_value;

  function new (string name = "csr_register");
    super.new(name);
  endfunction

    function void set_field(bit[63:0] value, int idx_high, int idx_low);
        csr_field field = new();
        field.field_value = value;
        field.idx_high = idx_high;
        field.idx_low = idx_low;
        field_queue.push_back(field);
    endfunction

    // update the last pushed field for illegal value
    function void set_field_illegal_value(bit[63:0] value);
        int idx;

        if (field_queue.size() != 0) begin
            idx = field_queue.size() - 1;
            field_queue[idx].illegal_value_arr[value] = 1;
        end
        else begin
            `uvm_fatal("fatal", $psprintf("field queue is empty, need to call set_field first"));
        end
    endfunction

    // update the last pushed field for ignore value
    function void set_field_ignore_value(bit[63:0] value);
        int idx;

        if (field_queue.size() != 0) begin
            idx = field_queue.size() - 1;
            field_queue[idx].ignore_value_arr[value] = 1;
        end
        else begin
            `uvm_fatal("fatal", $psprintf("field queue is empty, need to call set_field first"));
        end
    endfunction

    function void cal_reg_value();
        reg_value = 0;
        for (int i=0; i<field_queue.size(); i++) begin
            field_queue[i].get_field_mask();
            reg_value += (field_queue[i].field_value & field_queue[i].field_mask) << field_queue[i].idx_low;
        end
    endfunction

    function bit[63:0] get_field_data(bit[63:0] value, int idx_high, int idx_low);
        bit [63:0] result;
        bit [63:0] mask;

        mask = 0;
        for (int i=0; i<=(idx_high-idx_low); i++) begin
            mask += 1 << i;
        end

        result = (value >> idx_low) & mask;

        return result;
    endfunction

    function void set_all_field_value(bit[63:0] value);
        for (int i=0; i<field_queue.size(); i++) begin
            field_queue[i].field_value = get_field_data(value, field_queue[i].idx_high, field_queue[i].idx_low);
        end
    endfunction
endclass

class mem_range extends uvm_sequence_item;
    bit [63:0] min_addr;
    bit [63:0] max_addr;

    function new (string name = "mem_range");
    super.new(name);
  endfunction

    function bit is_addr_in_range(bit[63:0] addr);
        if (addr >= min_addr && addr <= max_addr) begin
            return 1;
        end
        else begin
            return 0;
        end
    endfunction
endclass

typedef enum {
    TYPE_CODE = 0,    // normal instruction code
    TYPE_BVEC = 1,    // boot vector
    TYPE_TVEC = 2,    // trap vector
    TYPE_BKDR_DATA = 3, // backdoor data
    TYPE_STACK = 4,   // stack
    TYPE_DATA = 5     // normal data
} region_type_e;

class mem_region extends uvm_sequence_item;
    region_type_e region_type;
    mem_range va_range[$];
    mem_range pa_range[$];

  function new (string name = "mem_region");
    super.new(name);
  endfunction

    function void set_va_range(bit[63:0] min, bit[63:0] max);
        mem_range range = new();
        range.min_addr = min;
        range.max_addr = max;
        va_range.push_back(range);
    endfunction

    function void set_pa_range(bit[63:0] min, bit[63:0] max);
        mem_range range = new();
        range.min_addr = min;
        range.max_addr = max;
        pa_range.push_back(range);
    endfunction

    function bit is_addr_in_va_range(bit[63:0] addr);
        bit found_addr = 0;

        for (int i=0; i<va_range.size(); i++) begin
            if (va_range[i].is_addr_in_range(addr) == 1) begin
                found_addr = 1;
                break;
            end
        end

        return found_addr;
    endfunction

    function bit is_addr_in_pa_range(bit[63:0] addr);
        bit found_addr = 0;

        for (int i=0; i<pa_range.size(); i++) begin
            if (pa_range[i].is_addr_in_range(addr) == 1) begin
                found_addr = 1;
                break;
            end
        end

        return found_addr;
    endfunction
endclass

class randc32;
  randc bit [5-1:0] val;
endclass

class riscv_base_seq extends uvm_sequence #(riscv_inst_base_txn);
  `uvm_object_utils(riscv_base_seq);

  bit [63:0] init_start_pc;
  bit [63:0] m_curr_pc;
  int seqlen_min;
    int seqlen_max;
  bit [63:0] reserve_mem_start_va;  // The start address va to hold pre-defined value which will be loaded into corresponding gpr
  bit [63:0] reserve_mem_start_pa;  // The start address pa to hold pre-defined value which will be loaded into corresponding gpr
    bit [63:0] stack_start_va;      // the start va address for stack
    int reserve_offset = 0;             // current reserve_mem_addr = reserve_mem_start_pa + reserve_offset
  bit [63:0] curr_mmode_isr_addr;   // Current address to store M-mode ISR code
  bit [63:0] curr_smode_isr_addr;   // Current address to store S-mode ISR code
  bit [63:0] init_timecmp;
    bit is_lsu_mis_align;
    bit random_pmp_cfg;

    // enable randomly assert interrupt pin.
    bit interrupt_en;

    // to ensure interrupt enable bit is valid for sure, not randomly enable
    bit interrupt_must_en;

    // nest exception case
    bit nest_expt_en;

    // mtimecmp CSR step length in trap handler to clear M timer interrupt
    // mtimecmp actual adding value = mtimecmp_step_length << 8. Note mtimecmp_step_length can't be bigger than 'h7ff
    int mtimecmp_step_length;

    // enable randomly config M-mode or U-mode in test_init()
    bit dis_usmode;
    bit dis_mmode;

  // knob to control mstatus.mprv
  bit mstatus_mprv;

    // knob to enable generating C-extension instructions in new random flow
    bit gen_rvc_en;

  // mtvec/stvec config
  bit [1:0] mtvec_mode;
  bit [1:0] stvec_mode;

  // fpu instruction enable
  bit fpu_inst_en;

  // disable S-mode to make sure test only run in M/U mode
    bit dis_smode;

  typedef enum {
    FIX_DONE = 0,         // fix is done successfully
    FIX_FAIL = 1,         // fix failed
    FIX_RETRY = 2,          // fix is not done completely, need to retry
        FIX_MODIFY = 3                  // can't find place to insert fix pc, modify current branch instrcution type to non-branch
  } fix_dead_loop_result_e;

  typedef enum {
    RETURN_PC = 0,          // return next pc for calculate_op(), GPR is updated normally to m_gpr[]
    RETURN_GPR = 1          // return dest GPR value, GPR is not updated to m_gpr[]
  } cal_op_type_e;

    typedef enum {
        PA_RANGE_RSVD = 0
    } pa_range_e;  // NEED_CHANGE

    typedef enum {
        PRIV_LEVEL_UMODE = 0,
        PRIV_LEVEL_SMODE = 1,
        PRIV_LEVEL_MMODE = 3
    } privilege_level_e;


    /////////////////////////////////
    // csr related configuration
    /////////////////////////////////
    bit [63:0] mepc;
    bit [1:0] mpp;
    bit mie;
    bit mpie;
    bit [63:0] sepc;
    bit [1:0] spp;
    bit sie;
    bit spie;
    bit mprv;
    bit mxr;
    bit tvm;
    bit tw;
    bit tsr;
    bit [3:0] satp_mode;
    bit [63:0] mscratch;
    bit [63:0] sscratch;
    bit [63:0] mtimecmp;
    bit [63:0] mcause;
    bit [63:0] scause;
    bit [63:0] cause;
    bit [63:0] medeleg;
    bit [63:0] mideleg;
    bit [63:0] minstret;
    bit [63:0] mcounteren;
    bit [63:0] scounteren;
    bit [1:0] fs;
    bit [2:0] frm;

    // trap vector
    bit [63:0] m_init_mmode_trap_vector;
    bit [63:0] m_curr_mmode_trap_vector;
    bit [63:0] m_init_smode_trap_vector;
    bit [63:0] m_curr_smode_trap_vector;

    pmpaddr_cfg  m_init_pmpaddr_cfg[`MAX_PMP_ADDR_NUM];
    pmpcfg_cfg   m_init_pmpcfg_cfg [`MAX_PMP_ADDR_NUM];

    // current privilege level
    privilege_level_e m_init_priv_level;
    privilege_level_e m_curr_priv_level;

  // the queue to store avaiable gpr for instructions to be used
  bit [63:0] gpr_queue[];
  int gpr_num;

  // queue for available fpr
  bit [4:0]  fpr_queue[];

  // store current gpr value
  bit[63:0] m_gpr[32];

  // store initial gpr value
  rand_gpr c_gpr;
    
    // reserve GPR to be used for TB, store backdoor memory base
    bit [4:0] reserve_gpr;

    // reserve GPR to be used for TB, store boot vector
    bit [4:0] reserve_gpr_boot;

    // reserve GPR to be used for TB, store stack address
    bit [4:0] reserve_gpr_stack;

    // reserve GPR to be used for TB, store instruction access fault exception jump step
    bit [4:0] reserve_gpr_iaf_step;
    bit [63:0] reserve_gpr_iaf_step_wdata;

    // reserve GPR to be used for TB, store last instruction access fault exception jump offset
    bit [4:0] reserve_gpr_iaf_offset;

    // array to store all reserved GPR
    bit rsvd_gpr_arr [*];
  
  // create a local copy of memory array to calculate memory opertion result
  // since riscv_mem's memory array can only be updated when instruction really executes in DUT
  bit [7:0] m_mem [*];

  // used to record pre-initialized memory content by init_gpr() and other user initial routine
    // also record generated intruction code in new random flow and randomized load data
  bit [7:0] m_init_mem[*];

  // store all generated instructions, index is va of pc
  riscv_inst_base_txn inst_arr[*];

    // store initial generated instructions, index is va of pc
    riscv_inst_base_txn init_inst_arr[*];

    // store all lsu pa which has been accessed before
    // used to make sure last self-loop instruction won't be accessed by previous LSU inst
    bit accessed_lsu_pa_arr[*];
  
    // TODO: confirm with Neo Fang that this is not needed.
    // instruction result from tb side intruction reference
    //riscv_inst_result_txn tb_exp_queue[$];

    // pc management
    bit m_boot_pc[*];
    bit m_tvec_pc[*];
    bit m_normal_pc[*];

    // memory regions
    mem_region m_code_region;
    mem_region m_bvec_region;
    mem_region m_tvec_region;
    mem_region m_bkdr_data_region;
    mem_region m_stack_region;
    mem_region m_data_region;

    // used pmp entry ids
    bit m_used_pmp_idx [int];  //TODO: use int for assoc array index type (discuss with Neo Fang)

  // max allowed same pc times, simulation will exit after reaching this value
  // the value is set according to cmod implementation
  int max_same_pc_times = `END_LOOP_PC_TIMES;

  // for TB timeout mechanism
  int init_seconds;
  int curr_seconds;
  int timeout_seconds;

    // to add branch instruction in trap handler
    // use this offset to prepare corresponding instructions when branch taken
    int trap_pc_offset = 0;
    int trap_pc_offset_smode = 0;

  //
  // variables used for branch control
  //
  bit [63:0] min_pc;  // the first instruction pc out of boot sequence

  int br_range;

  // queue to store avaiable pc to insert forward branch
  bit [63:0] insert_pc_queue[$];

  // queue to store all PCs in a dead loop, start from target_pc and end with branch_pc
  bit [63:0] loop_pc_queue[$];

  // the pc to insert forward branch instruction
  bit [63:0] insert_pc;

  // the index for insert_pc in insert_pc_queue
  int insert_pc_idx;

  // a loop is condidered as dead loop if reach this value
  int max_loop_times;

    //tmp varialbe
  bit [31:0] rnd,rnd1,rnd2,rnd3,rnd4,rnd5,rnd6,rnd7,rnd8,rnd9;

  rand int seqlen;
  constraint c_seqlen {seqlen inside {[seqlen_min:seqlen_max]};}

  // function/task
  extern function new (string name = "riscv_base_seq");
  extern function void gen_gpr_queue();
  extern function void gen_fpr_queue(int cnt=-1);
  extern function bit[63:0] sign_extend (bit[63:0] data, int size);
  extern function bit[63:0] m_load(bit[63:0] addr, int ld_byte, bit is_sext);
  extern function void m_store(bit[63:0] addr, bit [63:0] data, int st_byte);
  extern function bit[63:0] calculate_op(inst_type_e inst_type, bit[63:0] cpc, bit[4:0] rd, bit[4:0] rs1, bit[4:0] rs2, bit[31:0] imm, cal_op_type_e ctype=RETURN_PC);
  extern function void gen_inst_result();
  extern function void gen_curr_inst_result(bit[63:0] last_pc='hffff_ffff_ffff_ffff);
  extern function bit[31:0] gen_isr_inst_code_with_pc(inst_type_e inst_type, bit[4:0] rd, bit[4:0] rs1, bit[4:0] rs2, bit[31:0] imm, bit[63:0] pc, bit[255:0] pc_pa);
  extern task store_isr_inst_code(inst_type_e inst_type, bit[4:0] rd, bit[4:0] rs1, bit[4:0] rs2, bit[31:0] imm);
  extern task store_smode_isr_inst_code(inst_type_e inst_type, bit[4:0] rd, bit[4:0] rs1, bit[4:0] rs2, bit[31:0] imm);
  extern function void store_isr_inst_code_with_pc(inst_type_e inst_type, bit[4:0] rd, bit[4:0] rs1, bit[4:0] rs2, bit[31:0] imm, bit[63:0] pc);
  extern function void store_smode_isr_inst_code_with_pc(inst_type_e inst_type, bit[4:0] rd, bit[4:0] rs1, bit[4:0] rs2, bit[31:0] imm, bit[63:0] pc);
  extern task create_op(inst_type_e inst_type, bit[4:0] rd, bit[4:0] rs1, bit[4:0] rs2, bit[31:0] imm, bit is_key_inst=0, int rs3=-1);
  extern task create_op_with_pc(inst_type_e inst_type, bit[4:0] rd, bit[4:0] rs1, bit[4:0] rs2, bit[31:0] imm, bit[63:0] pc, int rs3=-1);
  extern task init_random_gpr();
  extern task init_gpr();
  extern task init_fpr(int cnt=0);
  extern task init_fcsr();
    extern task init_all_reserve_gpr();
    extern task create_op_init_reserve_gpr(bit[4:0] dest_gpr, bit[63:0] wdata, bit[4:0] tmp_gpr, bit[4:0] tmp_gpr_1);
    extern task create_op_ld_gpr(bit[4:0] gpr, bit[63:0] value);
    extern virtual task config_pmp_region();
    extern virtual task config_trap_vector();
    extern virtual task config_interrupt_en();
    extern virtual task config_delegation();
    extern virtual task config_riscv_mode();
    extern virtual task config_mtimecmp();
    extern virtual task init_pmp_cfg();
    extern virtual task config_mcounteren();
    extern virtual task config_mstatus();
  extern task create_final_op();
    extern task test_init();
  extern function bit[4:0] get_random_gpr();
  extern function bit[4:0] get_random_gpr_for_rd();
  extern function bit[4:0] get_random_non_zero_gpr();
    extern function bit[63:0] random_range_64(bit[63:0] min, bit[63:0] max);
    extern function bit[63:0] gen_fp_data(int sign=-1, int expo=-1, longint frac=-1);
    extern function bit[63:0] fp_data_delta(bit[63:0] fp_data_i);
  extern function bit is_load_inst(inst_type_e inst_type);
  extern function bit is_branch_inst(inst_type_e inst_type);
    extern function bit[63:0] get_field_value(bit[63:0] reg_value, int idx_high, int idx_low);
    extern function bit cal_csr(inst_type_e inst_type, bit[11:0] csr, bit[4:0] src, bit[4:0] rd);
    extern function bit check_csr_exception(inst_type_e inst_type, bit[11:0] csr, bit[4:0] src, bit[4:0] rd);
    extern function bit[63:0] get_csr_wdata(inst_type_e inst_type, bit[4:0] src, bit[63:0] ori_value);
    extern function csr_register get_csr_reg(bit[11:0] csr);
    extern function void get_csr_field(bit[11:0] csr, csr_register csr_reg);
    extern function void init_m_mem();
    extern function void init_csr();
    extern function bit check_single_region_validity(mem_region region);
    extern function bit check_all_region_validity();
    extern function bit[31:0] get_pmp_id(ref pmpcfg_cfg pmp_cfg);
    extern function void set_pmp_region(bit[63:0] region_start, bit[63:0] region_end);
    extern function bit is_in_boot_pc_range(bit[63:0] pc);
    extern function bit is_in_tvec_pc_range(bit[63:0] pc);
    extern function void store_inst_code(riscv_inst_base_txn tr);
    extern function int get_st_bytes(inst_type_e inst_type);
    extern function bit is_overlap_with_inst_code(bit[63:0] pa, int bytes, int code_size, bit[255:0] pc_pa[$]);
    extern function bit is_overlap_with_exist_pc(bit[63:0] addr, int bytes, bit is_fetch, ref bit[63:0] pc[$]);
    extern function bit[63:0] insert_random_inst_in_isr(bit[63:0] pc, bit is_exit_trap, privilege_level_e mode);
  extern function int get_system_time();

  // branch control functions
  extern function int check_target_addr(bit[63:0] addr);
  extern function bit gen_br_target(bit only_forward_jump, ref riscv_inst_base_txn tr);
  extern function bit gen_insert_pc_queue(riscv_inst_base_txn tr, bit[63:0] target_pc);
  extern function bit gen_insert_pc(riscv_inst_base_txn tr);
  extern function bit insert_jal(riscv_inst_base_txn tr, bit can_jump_off_loop);
  extern function fix_dead_loop_result_e fix_br_dead_loop(ref riscv_inst_base_txn tr, bit[63:0] target_addr);
  
  // LSU control function
  extern function bit gen_lsu_addr(bit[63:0] min_addr, bit[63:0] max_addr, ref riscv_inst_base_txn tr);
  extern function bit[63:0] get_lsu_va(riscv_inst_base_txn tr);
  extern function bit[63:0] get_lsu_pa(riscv_inst_base_txn tr);
  extern function int get_lsu_size(inst_type_e inst_type);
  extern function int get_fetch_size(inst_type_e inst_type);

    extern function bit check_lsu_exception(inst_type_e inst_type, bit[63:0] va);
    extern function void insert_lsu_bus_fault(inst_type_e inst_type, bit[63:0] addr);
    extern function void insert_fetch_bus_fault(bit[63:0] pc, int code_size);
    extern function bit check_fetch_fault_exception(bit[63:0] pc, int code_size);
    extern function bit get_legal_lsu_param(inst_type_e inst_type, ref bit[4:0] rs1, ref bit[63:0] min, ref bit[63:0] max);
    extern function bit is_valid_clsu_base(inst_type_e inst_type, bit[63:0] base);
  extern function int check_lsu_target_addr(inst_type_e inst_type, bit[63:0] addr, int bytes);

  // sequence valid function
  extern function void print_gpr();
  extern function bit gen_valid_sequence(int inst_num, ref bit[63:0] last_pc);
    extern function pa_range_e get_pa_range(bit[63:0] pa);
    extern function bit[63:0] va2pa(bit[63:0] va, bit is_fetch);
    extern function bit[63:0] pa2va(bit[63:0] pa, bit is_fetch);
    extern function bit check_mem_trans_access_violation(bit[63:0] va, int size, bit is_fetch, bit is_load);
    extern function bit check_mem_trans_access_violation_per_byte(bit[63:0] va, bit is_fetch, bit is_load);
    extern function bit check_page_fault_violation(bit[63:0] va, int size, bit is_fetch, bit is_load);
    extern function bit check_pmp_violation(bit[63:0] pa, bit is_fetch, bit is_load, int size);
    extern function bit check_pmp_cross_boundary(bit[63:0] pa_queue[$]);
    extern function bit[63:0] get_pa(bit[63:0] va, bit is_fetch, bit is_load);
    extern function void insert_inst_for_unexecuted_addr();
    extern function bit[1:0] rand_two_bits();
    extern function bit is_pc_accessed_by_lsu(bit[255:0] pc_pa, int code_size);
    extern function privilege_level_e get_curr_check_priv_level(bit is_fetch);


// NEED_CHANGE
virtual task init_random_pmp_cfg();
    pmpaddr_cfg pmpaddr_cfg_txn;
    pmpcfg_cfg  pmpcfg_cfg_txn;
    pmpaddr_cfg pmpaddr_cfg_txn_1;
    pmpcfg_cfg  pmpcfg_cfg_txn_1;
    int idx;
  int curr_idx = 0;
    bit [63:0] va_base;
    bit [63:0] pa_base;
    int has_overlap = 0;

    // for trap vector
    for (int i=0; i<m_tvec_region.va_range.size(); i++) begin
    idx = curr_idx;
    m_used_pmp_idx[idx] = 1;
    curr_idx++;

        pmpaddr_cfg_txn = new();
        pmpcfg_cfg_txn  = new();
        pmpcfg_cfg_txn.r = $urandom;
        pmpcfg_cfg_txn.w = 0;
        pmpcfg_cfg_txn.x = 1;
        if(i==0)
            pmpcfg_cfg_txn.a = `PMP_NAPOT;
        else begin
            pmpcfg_cfg_txn.a = (($urandom%5)==0) ? `PMP_TOR : `PMP_NAPOT;
        end
        pmpcfg_cfg_txn.s = $urandom;
        pmpcfg_cfg_txn.l = (($urandom%2)==0)  ? 0 : 1;
        void'(pmpcfg_cfg_txn.pack_cfg());
        pmpaddr_cfg_txn.min_addr = (m_tvec_region.pa_range[i].min_addr<m_tvec_region.va_range[i].min_addr? m_tvec_region.pa_range[i].min_addr: m_tvec_region.va_range[i].min_addr);
        pmpaddr_cfg_txn.max_addr = (m_tvec_region.pa_range[i].max_addr>m_tvec_region.va_range[i].max_addr? m_tvec_region.pa_range[i].max_addr: m_tvec_region.va_range[i].max_addr);
        pmpaddr_cfg_txn.cal_addr(pmpcfg_cfg_txn.a);
        if(pmpcfg_cfg_txn.a == `PMP_TOR) begin
            idx++;
            curr_idx++;
        m_used_pmp_idx[idx] = 1;
            pmpaddr_cfg_txn_1 = new();
            pmpcfg_cfg_txn_1  = new();
            pmpcfg_cfg_txn_1.a = 0;
            void'(pmpcfg_cfg_txn_1.pack_cfg());
            pmpaddr_cfg_txn_1.paddr = (pmpaddr_cfg_txn.min_addr>>2);
            m_init_pmpaddr_cfg[idx-1] = pmpaddr_cfg_txn_1;
            m_init_pmpcfg_cfg[idx-1]  = pmpcfg_cfg_txn_1;
        end
        m_init_pmpaddr_cfg[idx] = pmpaddr_cfg_txn;
        m_init_pmpcfg_cfg[idx]  = pmpcfg_cfg_txn;
    end

    //smode trap vector
  idx = curr_idx;
  m_used_pmp_idx[idx] = 1;
  curr_idx++;
    pmpaddr_cfg_txn = new();
    pmpcfg_cfg_txn  = new();
    pmpcfg_cfg_txn.r = $urandom;
    pmpcfg_cfg_txn.w = 0;
    pmpcfg_cfg_txn.x = 1;
    pmpcfg_cfg_txn.a = (($urandom%5)==0) ? `PMP_TOR : `PMP_NAPOT;
    pmpcfg_cfg_txn.s = $urandom;
    pmpcfg_cfg_txn.l = (($urandom%2)==0)  ? 0 : 1;
    void'(pmpcfg_cfg_txn.pack_cfg());
    pmpaddr_cfg_txn.min_addr = m_init_smode_trap_vector;
    pmpaddr_cfg_txn.max_addr = m_init_smode_trap_vector + 'h1000;
    pmpaddr_cfg_txn.cal_addr(pmpcfg_cfg_txn.a);
    if(pmpcfg_cfg_txn.a == `PMP_TOR) begin
        idx++;
        curr_idx++;
      m_used_pmp_idx[idx] = 1;
        pmpaddr_cfg_txn_1 = new();
        pmpcfg_cfg_txn_1  = new();
        pmpcfg_cfg_txn_1.a = 0;
        void'(pmpcfg_cfg_txn_1.pack_cfg());
        pmpaddr_cfg_txn_1.paddr = (pmpaddr_cfg_txn.min_addr>>2);
        m_init_pmpaddr_cfg[idx-1] = pmpaddr_cfg_txn_1;
        m_init_pmpcfg_cfg[idx-1]  = pmpcfg_cfg_txn_1;
    end
    m_init_pmpaddr_cfg[idx] = pmpaddr_cfg_txn;
    m_init_pmpcfg_cfg[idx]  = pmpcfg_cfg_txn;

    // for backdoor data
    for (int i=0; i<m_bkdr_data_region.va_range.size(); i++) begin
    idx = curr_idx;
    m_used_pmp_idx[idx] = 1;
    curr_idx++;

        pmpaddr_cfg_txn = new();
        pmpcfg_cfg_txn  = new();
        pmpcfg_cfg_txn.r = 1;
        pmpcfg_cfg_txn.w = 0;
        pmpcfg_cfg_txn.x = $urandom;
        pmpcfg_cfg_txn.a = (($urandom%5)==0) ? `PMP_TOR : `PMP_NAPOT;
        pmpcfg_cfg_txn.s = $urandom;
        pmpcfg_cfg_txn.l = (($urandom%2)==0)  ? 0 : 1;
        void'(pmpcfg_cfg_txn.pack_cfg());
        pmpaddr_cfg_txn.min_addr = (m_bkdr_data_region.pa_range[i].min_addr<m_bkdr_data_region.va_range[i].min_addr?m_bkdr_data_region.pa_range[i].min_addr:m_bkdr_data_region.va_range[i].min_addr);
        pmpaddr_cfg_txn.max_addr = (m_bkdr_data_region.pa_range[i].max_addr>m_bkdr_data_region.va_range[i].max_addr?m_bkdr_data_region.pa_range[i].max_addr:m_bkdr_data_region.va_range[i].max_addr);
        pmpaddr_cfg_txn.cal_addr(pmpcfg_cfg_txn.a);
        if(pmpcfg_cfg_txn.a == `PMP_TOR) begin
            idx++;
            curr_idx++;
        m_used_pmp_idx[idx] = 1;
            pmpaddr_cfg_txn_1 = new();
            pmpcfg_cfg_txn_1  = new();
            pmpcfg_cfg_txn_1.a = 0;
            void'(pmpcfg_cfg_txn_1.pack_cfg());
            pmpaddr_cfg_txn_1.paddr = (pmpaddr_cfg_txn.min_addr>>2);
            m_init_pmpaddr_cfg[idx-1] = pmpaddr_cfg_txn_1;
            m_init_pmpcfg_cfg[idx-1]  = pmpcfg_cfg_txn_1;
        end
        m_init_pmpaddr_cfg[idx] = pmpaddr_cfg_txn;
        m_init_pmpcfg_cfg[idx]  = pmpcfg_cfg_txn;
    end

    // for stack
    for (int i=0; i<m_stack_region.va_range.size(); i++) begin
    idx = curr_idx;
    m_used_pmp_idx[idx] = 1;
    curr_idx++;
        
        pmpaddr_cfg_txn = new();
        pmpcfg_cfg_txn  = new();
        pmpcfg_cfg_txn.r = 1;
        pmpcfg_cfg_txn.w = 1;
        pmpcfg_cfg_txn.x = 0;
        pmpcfg_cfg_txn.a = (($urandom%5)==0) ? `PMP_TOR : `PMP_NAPOT;
        pmpcfg_cfg_txn.s = $urandom;
        pmpcfg_cfg_txn.l = (($urandom%2)==0)  ? 0 : 1;
        void'(pmpcfg_cfg_txn.pack_cfg());
        pmpaddr_cfg_txn.min_addr = (m_stack_region.pa_range[i].min_addr<m_stack_region.va_range[i].min_addr?m_stack_region.pa_range[i].min_addr:m_stack_region.va_range[i].min_addr);
        pmpaddr_cfg_txn.max_addr = (m_stack_region.pa_range[i].max_addr>m_stack_region.va_range[i].max_addr?m_stack_region.pa_range[i].max_addr:m_stack_region.va_range[i].max_addr);
        pmpaddr_cfg_txn.cal_addr(pmpcfg_cfg_txn.a);
        if(pmpcfg_cfg_txn.a == `PMP_TOR) begin
            idx++;
            curr_idx++;
        m_used_pmp_idx[idx] = 1;
            pmpaddr_cfg_txn_1 = new();
            pmpcfg_cfg_txn_1  = new();
            pmpcfg_cfg_txn_1.a = 0;
            void'(pmpcfg_cfg_txn_1.pack_cfg());
            pmpaddr_cfg_txn_1.paddr = (pmpaddr_cfg_txn.min_addr>>2);
            m_init_pmpaddr_cfg[idx-1] = pmpaddr_cfg_txn_1;
            m_init_pmpcfg_cfg[idx-1]  = pmpcfg_cfg_txn_1;
        end


        m_init_pmpaddr_cfg[idx] = pmpaddr_cfg_txn;
        m_init_pmpcfg_cfg[idx]  = pmpcfg_cfg_txn;
    end

    // for boot vector
    for (int i=0; i<m_bvec_region.va_range.size(); i++) begin
    idx = curr_idx;
    m_used_pmp_idx[idx] = 1;
    curr_idx++;
        
        pmpaddr_cfg_txn = new();
        pmpcfg_cfg_txn  = new();
        pmpcfg_cfg_txn.r = $urandom;
        pmpcfg_cfg_txn.w = 0;
        pmpcfg_cfg_txn.x = 1;
        pmpcfg_cfg_txn.a = (($urandom%5)==0) ? `PMP_TOR : `PMP_NAPOT;
        pmpcfg_cfg_txn.s = $urandom;
        pmpcfg_cfg_txn.l = (($urandom%2)==0)  ? 0 : 1;
        void'(pmpcfg_cfg_txn.pack_cfg());
        pmpaddr_cfg_txn.min_addr = (m_bvec_region.pa_range[i].min_addr<m_bvec_region.va_range[i].min_addr?m_bvec_region.pa_range[i].min_addr:m_bvec_region.va_range[i].min_addr);
        pmpaddr_cfg_txn.max_addr = (m_bvec_region.pa_range[i].max_addr>m_bvec_region.va_range[i].max_addr?m_bvec_region.pa_range[i].max_addr:m_bvec_region.va_range[i].max_addr);
        pmpaddr_cfg_txn.cal_addr(pmpcfg_cfg_txn.a);
        if(pmpcfg_cfg_txn.a == `PMP_TOR) begin
            idx++;
            curr_idx++;
        m_used_pmp_idx[idx] = 1;
            pmpaddr_cfg_txn_1 = new();
            pmpcfg_cfg_txn_1  = new();
            pmpcfg_cfg_txn_1.a = 0;
            void'(pmpcfg_cfg_txn_1.pack_cfg());
            pmpaddr_cfg_txn_1.paddr = (pmpaddr_cfg_txn.min_addr>>2);
            m_init_pmpaddr_cfg[idx-1] = pmpaddr_cfg_txn_1;
            m_init_pmpcfg_cfg[idx-1]  = pmpcfg_cfg_txn_1;
        end

        m_init_pmpaddr_cfg[idx] = pmpaddr_cfg_txn;
        m_init_pmpcfg_cfg[idx]  = pmpcfg_cfg_txn;

    end

    // for code
    for (int i=0; i<m_code_region.va_range.size(); i++) begin
    idx = curr_idx;
    m_used_pmp_idx[idx] = 1;
    curr_idx++;
        pmpaddr_cfg_txn = new();
        pmpcfg_cfg_txn  = new();
        pmpcfg_cfg_txn.r = $urandom;
        pmpcfg_cfg_txn.w = 0;
        pmpcfg_cfg_txn.x = 1;
        pmpcfg_cfg_txn.a = (($urandom%5)==0) ? `PMP_TOR : `PMP_NAPOT;
        pmpcfg_cfg_txn.s = $urandom;
        pmpcfg_cfg_txn.l = (($urandom%2)==0)  ? 0 : 1;
        void'(pmpcfg_cfg_txn.pack_cfg());
        pmpaddr_cfg_txn.min_addr = (m_code_region.pa_range[i].min_addr<m_code_region.va_range[i].min_addr?m_code_region.pa_range[i].min_addr:m_code_region.va_range[i].min_addr);
        pmpaddr_cfg_txn.max_addr = (m_code_region.pa_range[i].max_addr>m_code_region.va_range[i].max_addr?m_code_region.pa_range[i].max_addr:m_code_region.va_range[i].max_addr);
        pmpaddr_cfg_txn.cal_addr(pmpcfg_cfg_txn.a);
        if(pmpcfg_cfg_txn.a == `PMP_TOR) begin
            idx++;
            curr_idx++;
        m_used_pmp_idx[idx] = 1;
            pmpaddr_cfg_txn_1 = new();
            pmpcfg_cfg_txn_1  = new();
            pmpcfg_cfg_txn_1.a = 0;
            void'(pmpcfg_cfg_txn_1.pack_cfg());
            pmpaddr_cfg_txn_1.paddr = (pmpaddr_cfg_txn.min_addr>>2);
            m_init_pmpaddr_cfg[idx-1] = pmpaddr_cfg_txn_1;
            m_init_pmpcfg_cfg[idx-1]  = pmpcfg_cfg_txn_1;
        end
        m_init_pmpaddr_cfg[idx] = pmpaddr_cfg_txn;
        m_init_pmpcfg_cfg[idx]  = pmpcfg_cfg_txn;
    end

    //check the pmp entry has not overlap
    for(int i=0; i<idx; i++) begin
        for(int j=0; j<idx; j++) begin
            if((i!=j) && (m_init_pmpcfg_cfg[i].a !=0) && (m_init_pmpcfg_cfg[j].a !=0)) begin
                if((m_init_pmpaddr_cfg[i].min_addr >= m_init_pmpaddr_cfg[j].min_addr) &&
                   ((m_init_pmpaddr_cfg[i].min_addr + m_init_pmpaddr_cfg[i].range) <= (m_init_pmpaddr_cfg[j].min_addr + m_init_pmpaddr_cfg[j].range)))
                   has_overlap = 1;
                if((m_init_pmpaddr_cfg[i].min_addr <= m_init_pmpaddr_cfg[j].min_addr) &&
                   ((m_init_pmpaddr_cfg[i].min_addr + m_init_pmpaddr_cfg[i].range) >= (m_init_pmpaddr_cfg[j].min_addr + m_init_pmpaddr_cfg[j].range)))
                   has_overlap = 1;
                if(has_overlap) break;
            end
        end
    end
    `uvm_info("debug", $psprintf("the reserved pmp entry number is 0x%x", idx), UVM_LOW)

    if(has_overlap) begin
        `uvm_info("debug", "the reserved pmp entry has overlap", UVM_LOW)
        pmpaddr_cfg_txn = new();
        pmpcfg_cfg_txn  = new();
        pmpaddr_cfg_txn.min_addr = 0;
        pmpaddr_cfg_txn.max_addr = 64'hffff_ffff_ffff_ffff;;
        pmpaddr_cfg_txn.cal_addr(`PMP_NAPOT);
        pmpcfg_cfg_txn.r = 1;
        pmpcfg_cfg_txn.w = 1;
        pmpcfg_cfg_txn.x = 1;
        pmpcfg_cfg_txn.a = `PMP_NAPOT;
        pmpcfg_cfg_txn.s = $urandom;
        pmpcfg_cfg_txn.l = (($urandom%2)==0)  ? 0 : 1;
        m_init_pmpaddr_cfg[0] = pmpaddr_cfg_txn;
        m_init_pmpcfg_cfg[0]  = pmpcfg_cfg_txn;
    end

    // for data
    if (m_data_region != null) begin
        for (int i=0; i<m_data_region.va_range.size(); i++) begin

            pmpaddr_cfg_txn = new();
            pmpcfg_cfg_txn = new();
            
      pmpcfg_cfg_txn.r = $urandom;
            pmpcfg_cfg_txn.w = $urandom;
            pmpcfg_cfg_txn.x = $urandom;
            pmpcfg_cfg_txn.a = (($urandom%5)==0) ? `PMP_TOR : `PMP_NAPOT;
            pmpcfg_cfg_txn.s = $urandom;
            pmpcfg_cfg_txn.l = $urandom;
            void'(pmpcfg_cfg_txn.pack_cfg());
            idx = get_pmp_id(pmpcfg_cfg_txn);
            pmpaddr_cfg_txn.min_addr = (m_data_region.pa_range[i].min_addr<m_data_region.va_range[i].min_addr?m_data_region.pa_range[i].min_addr:m_data_region.va_range[i].min_addr);
            pmpaddr_cfg_txn.max_addr = (m_data_region.pa_range[i].max_addr>m_data_region.va_range[i].max_addr?m_data_region.pa_range[i].max_addr:m_data_region.va_range[i].max_addr);
            pmpaddr_cfg_txn.cal_addr(pmpcfg_cfg_txn.a);
            if(pmpcfg_cfg_txn.a == `PMP_TOR) begin
                pmpaddr_cfg_txn_1 = new();
                pmpcfg_cfg_txn_1  = new();
                pmpcfg_cfg_txn_1.a = 0;
                void'(pmpcfg_cfg_txn_1.pack_cfg());
                pmpaddr_cfg_txn_1.paddr = (pmpaddr_cfg_txn.min_addr>>2);
                m_init_pmpaddr_cfg[idx-1] = pmpaddr_cfg_txn_1;
                m_init_pmpcfg_cfg[idx-1]  = pmpcfg_cfg_txn_1;
            end

            m_init_pmpaddr_cfg[idx] = pmpaddr_cfg_txn;
            m_init_pmpcfg_cfg[idx]  = pmpcfg_cfg_txn;
        end
    end

    while(m_used_pmp_idx.size() != `MAX_PMP_NUM) begin
            pmpaddr_cfg_txn = new();
            pmpcfg_cfg_txn = new();

            void'(pmpcfg_cfg_txn.randomize() with {
            // to make pmp violation not too frequent
            r dist {0:/1, 1:/2};
            w dist {0:/1, 1:/2};
            x dist {0:/1, 1:/2};
            a dist {0:/1, `PMP_NAPOT:/4, `PMP_NA4:/2, `PMP_TOR:/4};
            s dist {0:/1, 1:/2};
            l dist {0:/1, 1:/2};
            });
            idx = get_pmp_id(pmpcfg_cfg_txn); 
            void'(pmpcfg_cfg_txn.pack_cfg());

            void'(pmpaddr_cfg_txn.randomize() with { 
               //foreach (rsvd_region_queue[j]) {
               //     (pmpcfg_cfg_txn.a !=0) -> !(min_addr inside {[rsvd_region_queue[j].pa_range[0].min_addr:rsvd_region_queue[j].pa_range[0].max_addr]});
               //     (pmpcfg_cfg_txn.a !=0) -> !(max_addr inside {[rsvd_region_queue[j].pa_range[0].min_addr:rsvd_region_queue[j].pa_range[0].max_addr]});
               //     (pmpcfg_cfg_txn.a !=0) -> !(rsvd_region_queue[j].pa_range[0].min_addr inside {[min_addr:max_addr]});
               //     (pmpcfg_cfg_txn.a !=0) -> !(rsvd_region_queue[j].pa_range[0].max_addr inside {[min_addr:max_addr]});
               // }
                min_addr dist {
                //`ifdef RISCV_PA_EXTMEM1_EXISTS
                //    [`RISCV_PA_EXTMEM1_START :`RISCV_PA_EXTMEM1_END]:/1,
                //`endif
                //`ifdef RISCV_PA_EXTMEM2_EXISTS
                //    [`RISCV_PA_EXTMEM2_START :`RISCV_PA_EXTMEM2_END]:/1,
                //`endif
                //`ifdef RISCV_PA_EXTMEM3_EXISTS
                //    [`RISCV_PA_EXTMEM3_START :`RISCV_PA_EXTMEM3_END]:/1,
                //`endif
                //`ifdef RISCV_PA_EXTMEM4_EXISTS
                //    [`RISCV_PA_EXTMEM4_START :`RISCV_PA_EXTMEM4_END]:/1,
                //`endif
                    [0:64'hffff_ffff_ffff_ffff-1024]:/1
                };
                max_addr >= min_addr;
                solve min_addr before max_addr;
            });
            pmpaddr_cfg_txn.cal_addr(pmpcfg_cfg_txn.a);
            if(pmpcfg_cfg_txn.a == `PMP_TOR) begin
                pmpaddr_cfg_txn_1 = new();
                pmpcfg_cfg_txn_1  = new();
                pmpcfg_cfg_txn_1.a = 0;
                void'(pmpcfg_cfg_txn_1.pack_cfg());
                pmpaddr_cfg_txn_1.paddr = (pmpaddr_cfg_txn.min_addr>>2);
                m_init_pmpaddr_cfg[idx-1] = pmpaddr_cfg_txn_1;
                m_init_pmpcfg_cfg[idx-1]  = pmpcfg_cfg_txn_1;
            end

            m_init_pmpaddr_cfg[idx] = pmpaddr_cfg_txn;
            m_init_pmpcfg_cfg[idx]  = pmpcfg_cfg_txn;
    end

    for (int i=`BROM_USED_PMP; i<`MAX_PMP_NUM; i++) begin
        `uvm_info("debug", $psprintf("\nFor pmp region %2d: pmpaddr = 0x%16x, range = 0x%16x, base = 0x%16x, pmpcfg = %2x, pmpcfg.r = %2d, pmpcfg.w = %2d, pmpcfg.x = %2d, pmpcfg.a = %2d, pmpcfg.s = %2d, pmpcfg.l = %2d", i, m_init_pmpaddr_cfg[i].paddr, m_init_pmpaddr_cfg[i].range, m_init_pmpaddr_cfg[i].min_addr,  m_init_pmpcfg_cfg[i].value , m_init_pmpcfg_cfg[i].r, m_init_pmpcfg_cfg[i].w, m_init_pmpcfg_cfg[i].x, m_init_pmpcfg_cfg[i].a, m_init_pmpcfg_cfg[i].s, m_init_pmpcfg_cfg[i].l), UVM_LOW);
    end
endtask

// generate initial gpr value
virtual task gen_init_gpr();
    c_gpr = new();
  void'(c_gpr.randomize());
  for (int i=0; i<31; i++) begin
    `uvm_info("INIT_GPR_DUMP", $psprintf("Initial randomized gpr[%0d] = 0x%0x\n", i+1, c_gpr.gpr[i]), UVM_HIGH);
  end
endtask

// initialize M-mode direct mode ISR() and put corresponding instruction code into memory
// NEED_CHANGE, user can decide to use this or create their own
virtual task init_mmode_isr();
    bit [4:0] tmp_gpr;
    bit [4:0] mcause_gpr;
    bit [63:0] curr_pc;
    bit [63:0] next_pc;
    bit [63:0] iaf_handler_pc;
    bit [63:0] intr_handler_pc;
  bit [63:0] mtint_handler_pc;
  bit [63:0] msint_handler_pc;
  bit [63:0] seint_handler_pc;
  bit [63:0] stint_handler_pc;
  bit [63:0] ssint_handler_pc;
    bit [63:0] normal_handler_pc;
    int iaf_offset = 'h100;         // for instruction access fault handler code
    int intr_offset = 'h200;        // for interrupt handler code (M external interrupt)
  int msint_offset = 'h80;        // for M software interrupt
  int mtint_offset = 'h100;       // for M timer interrupt
  int seint_offset = 'h180;       // for S external interrupt
  int stint_offset = 'h200;       // for S timer interrupt
  int ssint_offset = 'h280;       // for S software interrupt
    bit [31:0] imm;
    bit [31:0] tmp_gpr_stack_offset;    // offset from latest stack pointer
    bit [31:0] mcause_gpr_stack_offset; // offset from latest stack pointer
    bit [31:0] ori_stack_offset;        // offset from latest stack pointer

  tmp_gpr = $urandom_range(1, 31);
    while (rsvd_gpr_arr.exists(tmp_gpr)) begin
      tmp_gpr = $urandom_range(1, 31);
    end

  mcause_gpr = $urandom_range(1, 31);
    while (rsvd_gpr_arr.exists(mcause_gpr) || mcause_gpr == tmp_gpr) begin
      mcause_gpr = $urandom_range(1, 31);
    end

    curr_pc = m_init_mmode_trap_vector;

    // save context
    next_pc = insert_random_inst_in_isr(curr_pc, 0, PRIV_LEVEL_MMODE);
    curr_pc = next_pc;
    store_isr_inst_code_with_pc(OP_ADDI, reserve_gpr_stack, reserve_gpr_stack, 0, 8, curr_pc);
    curr_pc += 4;
    store_isr_inst_code_with_pc(OP_SD, 0, reserve_gpr_stack, tmp_gpr, 0, curr_pc);
    curr_pc += 4;
    store_isr_inst_code_with_pc(OP_ADDI, reserve_gpr_stack, reserve_gpr_stack, 0, 8, curr_pc);
    curr_pc += 4;
    store_isr_inst_code_with_pc(OP_SD, 0, reserve_gpr_stack, mcause_gpr, 0, curr_pc);
    curr_pc += 4;

    mcause_gpr_stack_offset = signed'(0);   // mcause_gpr (latest_pointer - 0)
    tmp_gpr_stack_offset = signed'(-8);     // tmp_gpr (latest_pointer - 8)
    ori_stack_offset = signed'(-16);        // original stack address (lastest_pointer - 16)

    // get mcause
    store_isr_inst_code_with_pc(OP_CSRRS, mcause_gpr, 0, 0, (`CSR_MCAUSE << 5), curr_pc);
    curr_pc += 4;

    store_isr_inst_code_with_pc(OP_SLTI, tmp_gpr, mcause_gpr, 0, 'hfff, curr_pc);  // mcause by interrupt is 64'b1xxxxxxx
    curr_pc += 4;
    store_isr_inst_code_with_pc(OP_BNE, 0, tmp_gpr, 0, intr_offset, curr_pc); // jump to curr_pc+intr_offset if it's interrupt
    intr_handler_pc = curr_pc + intr_offset;

    curr_pc += 4;
    imm = signed'(0 - `RISCV_CSR_MCAUSE_EXCODE_IACC_FAULT);
    store_isr_inst_code_with_pc(OP_ADDI, tmp_gpr, mcause_gpr, 0, imm, curr_pc);
    curr_pc += 4;
    store_isr_inst_code_with_pc(OP_BEQ, 0, tmp_gpr, 0, iaf_offset, curr_pc); // jump to curr_pc+iaf_offset if it's instruction access fault exception
    iaf_handler_pc = curr_pc + iaf_offset;

    curr_pc += 4;
    imm = signed'(0 - `RISCV_CSR_MCAUSE_EXCODE_IPAGE_FAULT);
    store_isr_inst_code_with_pc(OP_ADDI, tmp_gpr, mcause_gpr, 0, imm, curr_pc);
    curr_pc += 4;
    store_isr_inst_code_with_pc(OP_BEQ, 0, tmp_gpr, 0, iaf_offset-8, curr_pc); // jump to iaf_handler_pc (beq_iaf_pc+8+iaf_offset-8) if it's instruction page fault exception

    curr_pc += 4;
    normal_handler_pc = curr_pc;
    store_isr_inst_code_with_pc(OP_CSRRS, tmp_gpr, 0, 0, (`CSR_MEPC << 5), curr_pc);
    curr_pc += 4;
    store_isr_inst_code_with_pc(OP_ADDI, tmp_gpr, tmp_gpr, 0, 4, curr_pc);
    curr_pc += 4;
    store_isr_inst_code_with_pc(OP_CSRRW, 0, tmp_gpr, 0, (`CSR_MEPC << 5), curr_pc);
    curr_pc += 4;
    store_isr_inst_code_with_pc(OP_LD, tmp_gpr, reserve_gpr_stack, 0, tmp_gpr_stack_offset, curr_pc);  // tmp_gpr
    curr_pc += 4;
    store_isr_inst_code_with_pc(OP_LD, mcause_gpr, reserve_gpr_stack, 0, mcause_gpr_stack_offset, curr_pc);  // mcause_gpr
    curr_pc += 4;
    store_isr_inst_code_with_pc(OP_ADDI, reserve_gpr_stack, reserve_gpr_stack, 0, ori_stack_offset, curr_pc);  // restore stack pointer
    curr_pc += 4;
    next_pc = insert_random_inst_in_isr(curr_pc, 1, PRIV_LEVEL_MMODE);
    curr_pc = next_pc;
    store_isr_inst_code_with_pc(OP_MRET, 0, 0, 0, 0, curr_pc);

    // instruction access fault handler
    curr_pc = iaf_handler_pc;
    store_isr_inst_code_with_pc(OP_ADD, tmp_gpr, reserve_gpr_iaf_step, reserve_gpr_iaf_offset, 0, curr_pc);
    curr_pc += 4;
    store_isr_inst_code_with_pc(OP_ADDI, reserve_gpr_iaf_offset, tmp_gpr, 0, 0, curr_pc);
    curr_pc += 4;
    store_isr_inst_code_with_pc(OP_ADD, tmp_gpr, tmp_gpr, reserve_gpr_boot, 0, curr_pc);
    curr_pc += 4;
    store_isr_inst_code_with_pc(OP_CSRRW, 0, tmp_gpr, 0, (`CSR_MEPC << 5), curr_pc);
    curr_pc += 4;
    store_isr_inst_code_with_pc(OP_LD, tmp_gpr, reserve_gpr_stack, 0, tmp_gpr_stack_offset, curr_pc);  // tmp_gpr
    curr_pc += 4;
    store_isr_inst_code_with_pc(OP_LD, mcause_gpr, reserve_gpr_stack, 0, mcause_gpr_stack_offset, curr_pc);  // mcause_gpr
    curr_pc += 4;
    store_isr_inst_code_with_pc(OP_ADDI, reserve_gpr_stack, reserve_gpr_stack, 0, ori_stack_offset, curr_pc);  // restore stack pointer
    curr_pc += 4;
    next_pc = insert_random_inst_in_isr(curr_pc, 1, PRIV_LEVEL_MMODE);
    curr_pc = next_pc;
    store_isr_inst_code_with_pc(OP_MRET, 0, 0, 0, 0, curr_pc);

    // interrupt handler
    curr_pc = intr_handler_pc;
  store_isr_inst_code_with_pc(OP_ANDI, mcause_gpr, mcause_gpr, 0, 'hf, curr_pc);  // mask interrupt bit (mcause[63])
    
    curr_pc += 4;
    imm = signed'(0 - `RISCV_CSR_MCAUSE_EXCODE_M_SWINT);
  store_isr_inst_code_with_pc(OP_ADDI, tmp_gpr, mcause_gpr, 0, imm, curr_pc);
    curr_pc += 4;
  store_isr_inst_code_with_pc(OP_BEQ, 0, tmp_gpr, 0, msint_offset, curr_pc);
  msint_handler_pc = curr_pc + msint_offset;

    curr_pc += 4;
    imm = signed'(0 - `RISCV_CSR_MCAUSE_EXCODE_M_TINT);
  store_isr_inst_code_with_pc(OP_ADDI, tmp_gpr, mcause_gpr, 0, imm, curr_pc);
    curr_pc += 4;
  store_isr_inst_code_with_pc(OP_BEQ, 0, tmp_gpr, 0, mtint_offset, curr_pc);
  mtint_handler_pc = curr_pc + mtint_offset;

    curr_pc += 4;
    imm = signed'(0 - `RISCV_CSR_MCAUSE_EXCODE_S_EINT);
  store_isr_inst_code_with_pc(OP_ADDI, tmp_gpr, mcause_gpr, 0, imm, curr_pc);
    curr_pc += 4;
  store_isr_inst_code_with_pc(OP_BEQ, 0, tmp_gpr, 0, seint_offset, curr_pc);
  seint_handler_pc = curr_pc + seint_offset;

    curr_pc += 4;
    imm = signed'(0 - `RISCV_CSR_MCAUSE_EXCODE_S_TINT);
  store_isr_inst_code_with_pc(OP_ADDI, tmp_gpr, mcause_gpr, 0, imm, curr_pc);
    curr_pc += 4;
  store_isr_inst_code_with_pc(OP_BEQ, 0, tmp_gpr, 0, stint_offset, curr_pc);
  stint_handler_pc = curr_pc + stint_offset;

    curr_pc += 4;
    imm = signed'(0 - `RISCV_CSR_MCAUSE_EXCODE_S_SWINT);
  store_isr_inst_code_with_pc(OP_ADDI, tmp_gpr, mcause_gpr, 0, imm, curr_pc);
    curr_pc += 4;
  store_isr_inst_code_with_pc(OP_BEQ, 0, tmp_gpr, 0, ssint_offset, curr_pc);
  ssint_handler_pc = curr_pc + ssint_offset;
    
  // for M external interrupt
    curr_pc += 4;
    store_isr_inst_code_with_pc(OP_LD, tmp_gpr, reserve_gpr_stack, 0, tmp_gpr_stack_offset, curr_pc);  // tmp_gpr
    curr_pc += 4;
    store_isr_inst_code_with_pc(OP_LD, mcause_gpr, reserve_gpr_stack, 0, mcause_gpr_stack_offset, curr_pc);  // mcause_gpr
    curr_pc += 4;
    store_isr_inst_code_with_pc(OP_ADDI, reserve_gpr_stack, reserve_gpr_stack, 0, ori_stack_offset, curr_pc);  // restore stack pointer
    curr_pc += 4;
    next_pc = insert_random_inst_in_isr(curr_pc, 1, PRIV_LEVEL_MMODE);
    curr_pc = next_pc;
    store_isr_inst_code_with_pc(OP_MRET, 0, 0, 0, 0, curr_pc);

  // for M software interrupt
  curr_pc = msint_handler_pc;
    store_isr_inst_code_with_pc(OP_LD, tmp_gpr, reserve_gpr_stack, 0, tmp_gpr_stack_offset, curr_pc);  // tmp_gpr
    curr_pc += 4;
    store_isr_inst_code_with_pc(OP_LD, mcause_gpr, reserve_gpr_stack, 0, mcause_gpr_stack_offset, curr_pc);  // mcause_gpr
    curr_pc += 4;
    store_isr_inst_code_with_pc(OP_ADDI, reserve_gpr_stack, reserve_gpr_stack, 0, ori_stack_offset, curr_pc);  // restore stack pointer
    curr_pc += 4;
    next_pc = insert_random_inst_in_isr(curr_pc, 1, PRIV_LEVEL_MMODE);
    curr_pc = next_pc;
    store_isr_inst_code_with_pc(OP_MRET, 0, 0, 0, 0, curr_pc);

  // for M timer interrupt
  curr_pc = mtint_handler_pc;
  store_isr_inst_code_with_pc(OP_CSRRC, tmp_gpr, 0, 0, (`CSR_MTIMECMP << 5), curr_pc);
    curr_pc += 4;
    store_isr_inst_code_with_pc(OP_ADDI, mcause_gpr, 0, 0, mtimecmp_step_length, curr_pc);
    curr_pc += 4;
    store_isr_inst_code_with_pc(OP_SLLI, mcause_gpr, mcause_gpr, 0, 8, curr_pc);  // mcause_gpr = mtimecmp_step_length << 8
    curr_pc += 4;
  store_isr_inst_code_with_pc(OP_ADD, tmp_gpr, tmp_gpr, mcause_gpr, 0, curr_pc);
    curr_pc += 4;
  store_isr_inst_code_with_pc(OP_CSRRW, 0, tmp_gpr, 0, (`CSR_MTIMECMP << 5), curr_pc);
    curr_pc += 4;
    store_isr_inst_code_with_pc(OP_LD, tmp_gpr, reserve_gpr_stack, 0, tmp_gpr_stack_offset, curr_pc);  // tmp_gpr
    curr_pc += 4;
    store_isr_inst_code_with_pc(OP_LD, mcause_gpr, reserve_gpr_stack, 0, mcause_gpr_stack_offset, curr_pc);  // mcause_gpr
    curr_pc += 4;
    store_isr_inst_code_with_pc(OP_ADDI, reserve_gpr_stack, reserve_gpr_stack, 0, ori_stack_offset, curr_pc);  // restore stack pointer
    curr_pc += 4;
    next_pc = insert_random_inst_in_isr(curr_pc, 1, PRIV_LEVEL_MMODE);
    curr_pc = next_pc;
    store_isr_inst_code_with_pc(OP_MRET, 0, 0, 0, 0, curr_pc);

  // for S external interrupt
  curr_pc = seint_handler_pc;
    store_isr_inst_code_with_pc(OP_ADDI, tmp_gpr, 0, 0, 1, curr_pc);
    curr_pc += 4;
    store_isr_inst_code_with_pc(OP_SLLI, tmp_gpr, tmp_gpr, 0, 9, curr_pc);  // seip is mip[9]
    curr_pc += 4;
    store_isr_inst_code_with_pc(OP_CSRRC, 0, tmp_gpr, 0, (`CSR_MIP << 5), curr_pc);
    curr_pc += 4;
    store_isr_inst_code_with_pc(OP_LD, tmp_gpr, reserve_gpr_stack, 0, tmp_gpr_stack_offset, curr_pc);  // tmp_gpr
    curr_pc += 4;
    store_isr_inst_code_with_pc(OP_LD, mcause_gpr, reserve_gpr_stack, 0, mcause_gpr_stack_offset, curr_pc);  // mcause_gpr
    curr_pc += 4;
    store_isr_inst_code_with_pc(OP_ADDI, reserve_gpr_stack, reserve_gpr_stack, 0, ori_stack_offset, curr_pc);  // restore stack pointer
    curr_pc += 4;
    next_pc = insert_random_inst_in_isr(curr_pc, 1, PRIV_LEVEL_MMODE);
    curr_pc = next_pc;
    store_isr_inst_code_with_pc(OP_MRET, 0, 0, 0, 0, curr_pc);

  // for S timer interrupt
  curr_pc = stint_handler_pc;
    store_isr_inst_code_with_pc(OP_ADDI, tmp_gpr, 0, 0, 1, curr_pc);
    curr_pc += 4;
    store_isr_inst_code_with_pc(OP_SLLI, tmp_gpr, tmp_gpr, 0, 5, curr_pc);  // stip is mip[5]
    curr_pc += 4;
    store_isr_inst_code_with_pc(OP_CSRRC, 0, tmp_gpr, 0, (`CSR_MIP << 5), curr_pc);
    curr_pc += 4;
    store_isr_inst_code_with_pc(OP_LD, tmp_gpr, reserve_gpr_stack, 0, tmp_gpr_stack_offset, curr_pc);  // tmp_gpr
    curr_pc += 4;
    store_isr_inst_code_with_pc(OP_LD, mcause_gpr, reserve_gpr_stack, 0, mcause_gpr_stack_offset, curr_pc);  // mcause_gpr
    curr_pc += 4;
    store_isr_inst_code_with_pc(OP_ADDI, reserve_gpr_stack, reserve_gpr_stack, 0, ori_stack_offset, curr_pc);  // restore stack pointer
    curr_pc += 4;
    next_pc = insert_random_inst_in_isr(curr_pc, 1, PRIV_LEVEL_MMODE);
    curr_pc = next_pc;
    store_isr_inst_code_with_pc(OP_MRET, 0, 0, 0, 0, curr_pc);

  // for S software interrupt
  curr_pc = ssint_handler_pc;
    store_isr_inst_code_with_pc(OP_ADDI, tmp_gpr, 0, 0, 1, curr_pc);
    curr_pc += 4;
    store_isr_inst_code_with_pc(OP_SLLI, tmp_gpr, tmp_gpr, 0, 1, curr_pc);  // ssip is mip[1]
    curr_pc += 4;
    store_isr_inst_code_with_pc(OP_CSRRC, 0, tmp_gpr, 0, (`CSR_MIP << 5), curr_pc);
    curr_pc += 4;
    store_isr_inst_code_with_pc(OP_LD, tmp_gpr, reserve_gpr_stack, 0, tmp_gpr_stack_offset, curr_pc);  // tmp_gpr
    curr_pc += 4;
    store_isr_inst_code_with_pc(OP_LD, mcause_gpr, reserve_gpr_stack, 0, mcause_gpr_stack_offset, curr_pc);  // mcause_gpr
    curr_pc += 4;
    store_isr_inst_code_with_pc(OP_ADDI, reserve_gpr_stack, reserve_gpr_stack, 0, ori_stack_offset, curr_pc);  // restore stack pointer
    curr_pc += 4;
    next_pc = insert_random_inst_in_isr(curr_pc, 1, PRIV_LEVEL_MMODE);
    curr_pc = next_pc;
    store_isr_inst_code_with_pc(OP_MRET, 0, 0, 0, 0, curr_pc);
endtask

// initialize M-mode vectored mode ISR() and put corresponding instruction code into memory
// NEED_CHANGE, user can decide to use this or create their own
virtual task init_mmode_vectored_isr();
    bit [4:0] tmp_gpr;
    bit [4:0] mcause_gpr;
    bit [63:0] curr_pc;
    bit [63:0] next_pc;
    bit [63:0] meint_handler_pc;
  bit [63:0] mtint_handler_pc;
  bit [63:0] msint_handler_pc;
  bit [63:0] seint_handler_pc;
  bit [63:0] stint_handler_pc;
  bit [63:0] ssint_handler_pc;
  bit [63:0] expt_handler_pc;
    bit [63:0] iaf_handler_pc;
    bit [63:0] normal_handler_pc;
    int meint_offset = 'h100;       // for M external interrupt
  int mtint_offset = 'h180;       // for M timer interrupt
  int msint_offset = 'h200;       // for M software interrupt
  int seint_offset = 'h280;       // for S external interrupt
  int stint_offset = 'h300;       // for S timer interrupt
  int ssint_offset = 'h380;       // for S software interrupt
  int expt_offset = 'h400;        // for exception
    int iaf_offset = 'h480;         // for instruction access fault handler code
    bit [31:0] imm;
    bit [31:0] tmp_gpr_stack_offset;    // offset from latest stack pointer
    bit [31:0] mcause_gpr_stack_offset; // offset from latest stack pointer
    bit [31:0] ori_stack_offset;        // offset from latest stack pointer

  tmp_gpr = $urandom_range(1, 31);
    while (rsvd_gpr_arr.exists(tmp_gpr)) begin
      tmp_gpr = $urandom_range(1, 31);
    end

  mcause_gpr = $urandom_range(1, 31);
    while (rsvd_gpr_arr.exists(mcause_gpr) || mcause_gpr == tmp_gpr) begin
      mcause_gpr = $urandom_range(1, 31);
    end

    curr_pc = m_init_mmode_trap_vector;
  store_isr_inst_code_with_pc(OP_JAL, 0, 0, 0, expt_offset, curr_pc); // jump to curr_pc+expt_offset if it's exception
    expt_handler_pc = curr_pc + expt_offset;

    curr_pc = m_init_mmode_trap_vector + 4 * `RISCV_CSR_MCAUSE_EXCODE_M_EINT;
  store_isr_inst_code_with_pc(OP_JAL, 0, 0, 0, meint_offset, curr_pc); // jump to curr_pc+meint_offset if it's M external interrupt
    meint_handler_pc = curr_pc + meint_offset;

    curr_pc = m_init_mmode_trap_vector + 4 * `RISCV_CSR_MCAUSE_EXCODE_M_TINT;
  store_isr_inst_code_with_pc(OP_JAL, 0, 0, 0, mtint_offset, curr_pc); // jump to curr_pc+mtint_offset if it's M timer interrupt
    mtint_handler_pc = curr_pc + mtint_offset;

    curr_pc = m_init_mmode_trap_vector + 4 * `RISCV_CSR_MCAUSE_EXCODE_M_SWINT;
  store_isr_inst_code_with_pc(OP_JAL, 0, 0, 0, msint_offset, curr_pc); // jump to curr_pc+msint_offset if it's M software interrupt
    msint_handler_pc = curr_pc + msint_offset;

  curr_pc = m_init_mmode_trap_vector + 4 * `RISCV_CSR_MCAUSE_EXCODE_S_EINT;
  store_isr_inst_code_with_pc(OP_JAL, 0, 0, 0, seint_offset, curr_pc); // jump to curr_pc+seint_offset if it's S external interrupt
    seint_handler_pc = curr_pc + seint_offset;

    curr_pc = m_init_mmode_trap_vector + 4 * `RISCV_CSR_MCAUSE_EXCODE_S_TINT;
  store_isr_inst_code_with_pc(OP_JAL, 0, 0, 0, stint_offset, curr_pc); // jump to curr_pc+stint_offset if it's S timer interrupt
    stint_handler_pc = curr_pc + stint_offset;

    curr_pc = m_init_mmode_trap_vector + 4 * `RISCV_CSR_MCAUSE_EXCODE_S_SWINT;
  store_isr_inst_code_with_pc(OP_JAL, 0, 0, 0, ssint_offset, curr_pc); // jump to curr_pc+ssint_offset if it's S software interrupt
    ssint_handler_pc = curr_pc + ssint_offset;
    
  // exception handler
  curr_pc = expt_handler_pc;

    // save context
    store_isr_inst_code_with_pc(OP_ADDI, reserve_gpr_stack, reserve_gpr_stack, 0, 8, curr_pc);
    curr_pc += 4;
    store_isr_inst_code_with_pc(OP_SD, 0, reserve_gpr_stack, tmp_gpr, 0, curr_pc);
    curr_pc += 4;
    store_isr_inst_code_with_pc(OP_ADDI, reserve_gpr_stack, reserve_gpr_stack, 0, 8, curr_pc);
    curr_pc += 4;
    store_isr_inst_code_with_pc(OP_SD, 0, reserve_gpr_stack, mcause_gpr, 0, curr_pc);
    curr_pc += 4;

    mcause_gpr_stack_offset = signed'(0);   // mcause_gpr (latest_pointer - 0)
    tmp_gpr_stack_offset = signed'(-8);     // tmp_gpr (latest_pointer - 8)
    ori_stack_offset = signed'(-16);        // original stack address (lastest_pointer - 16)

    // get mcause
    store_isr_inst_code_with_pc(OP_CSRRS, mcause_gpr, 0, 0, (`CSR_MCAUSE << 5), curr_pc);
    curr_pc += 4;

    imm = signed'(0 - `RISCV_CSR_MCAUSE_EXCODE_IACC_FAULT);
    store_isr_inst_code_with_pc(OP_ADDI, tmp_gpr, mcause_gpr, 0, imm, curr_pc);
    curr_pc += 4;
    store_isr_inst_code_with_pc(OP_BEQ, 0, tmp_gpr, 0, iaf_offset, curr_pc); // jump to curr_pc+iaf_offset if it's instruction access fault exception
    iaf_handler_pc = curr_pc + iaf_offset;

    curr_pc += 4;
    imm = signed'(0 - `RISCV_CSR_MCAUSE_EXCODE_IPAGE_FAULT);
    store_isr_inst_code_with_pc(OP_ADDI, tmp_gpr, mcause_gpr, 0, imm, curr_pc);
    curr_pc += 4;
    store_isr_inst_code_with_pc(OP_BEQ, 0, tmp_gpr, 0, iaf_offset-8, curr_pc); // jump to iaf_handler_pc (beq_iaf_pc+8+iaf_offset-8) if it's instruction page fault exception

    curr_pc += 4;
    normal_handler_pc = curr_pc;
    store_isr_inst_code_with_pc(OP_CSRRS, tmp_gpr, 0, 0, (`CSR_MEPC << 5), curr_pc);
    curr_pc += 4;
    store_isr_inst_code_with_pc(OP_ADDI, tmp_gpr, tmp_gpr, 0, 4, curr_pc);
    curr_pc += 4;
    store_isr_inst_code_with_pc(OP_CSRRW, 0, tmp_gpr, 0, (`CSR_MEPC << 5), curr_pc);
    curr_pc += 4;
    store_isr_inst_code_with_pc(OP_LD, tmp_gpr, reserve_gpr_stack, 0, tmp_gpr_stack_offset, curr_pc);  // tmp_gpr
    curr_pc += 4;
    store_isr_inst_code_with_pc(OP_LD, mcause_gpr, reserve_gpr_stack, 0, mcause_gpr_stack_offset, curr_pc);  // mcause_gpr
    curr_pc += 4;
    store_isr_inst_code_with_pc(OP_ADDI, reserve_gpr_stack, reserve_gpr_stack, 0, ori_stack_offset, curr_pc);  // restore stack pointer
    curr_pc += 4;
    next_pc = insert_random_inst_in_isr(curr_pc, 1, PRIV_LEVEL_MMODE);
    curr_pc = next_pc;
    store_isr_inst_code_with_pc(OP_MRET, 0, 0, 0, 0, curr_pc);

    // instruction access fault handler
    curr_pc = iaf_handler_pc;
    store_isr_inst_code_with_pc(OP_ADD, tmp_gpr, reserve_gpr_iaf_step, reserve_gpr_iaf_offset, 0, curr_pc);
    curr_pc += 4;
    store_isr_inst_code_with_pc(OP_ADDI, reserve_gpr_iaf_offset, tmp_gpr, 0, 0, curr_pc);
    curr_pc += 4;
    store_isr_inst_code_with_pc(OP_ADD, tmp_gpr, tmp_gpr, reserve_gpr_boot, 0, curr_pc);
    curr_pc += 4;
    store_isr_inst_code_with_pc(OP_CSRRW, 0, tmp_gpr, 0, (`CSR_MEPC << 5), curr_pc);
    curr_pc += 4;
    store_isr_inst_code_with_pc(OP_LD, tmp_gpr, reserve_gpr_stack, 0, tmp_gpr_stack_offset, curr_pc);  // tmp_gpr
    curr_pc += 4;
    store_isr_inst_code_with_pc(OP_LD, mcause_gpr, reserve_gpr_stack, 0, mcause_gpr_stack_offset, curr_pc);  // mcause_gpr
    curr_pc += 4;
    store_isr_inst_code_with_pc(OP_ADDI, reserve_gpr_stack, reserve_gpr_stack, 0, ori_stack_offset, curr_pc);  // restore stack pointer
    curr_pc += 4;
    next_pc = insert_random_inst_in_isr(curr_pc, 1, PRIV_LEVEL_MMODE);
    curr_pc = next_pc;
    store_isr_inst_code_with_pc(OP_MRET, 0, 0, 0, 0, curr_pc);

    // M external interrupt handler
    curr_pc = meint_handler_pc;
    next_pc = insert_random_inst_in_isr(curr_pc, 1, PRIV_LEVEL_MMODE);
    curr_pc = next_pc;
    store_isr_inst_code_with_pc(OP_MRET, 0, 0, 0, 0, curr_pc);

  // for M software interrupt
  curr_pc = msint_handler_pc;
    next_pc = insert_random_inst_in_isr(curr_pc, 1, PRIV_LEVEL_MMODE);
    curr_pc = next_pc;
    store_isr_inst_code_with_pc(OP_MRET, 0, 0, 0, 0, curr_pc);

    mcause_gpr_stack_offset = signed'(0);   // mcause_gpr (latest_pointer - 0)
    tmp_gpr_stack_offset = signed'(-8);     // tmp_gpr (latest_pointer - 8)
    ori_stack_offset = signed'(-16);        // original stack address (lastest_pointer - 16)

  // for M timer interrupt
  curr_pc = mtint_handler_pc;
    store_isr_inst_code_with_pc(OP_ADDI, reserve_gpr_stack, reserve_gpr_stack, 0, 8, curr_pc);
    curr_pc += 4;
    store_isr_inst_code_with_pc(OP_SD, 0, reserve_gpr_stack, tmp_gpr, 0, curr_pc);
    curr_pc += 4;
    store_isr_inst_code_with_pc(OP_ADDI, reserve_gpr_stack, reserve_gpr_stack, 0, 8, curr_pc);
    curr_pc += 4;
    store_isr_inst_code_with_pc(OP_SD, 0, reserve_gpr_stack, mcause_gpr, 0, curr_pc);
    curr_pc += 4;
  store_isr_inst_code_with_pc(OP_CSRRC, tmp_gpr, 0, 0, (`CSR_MTIMECMP << 5), curr_pc);
    curr_pc += 4;
    store_isr_inst_code_with_pc(OP_ADDI, mcause_gpr, 0, 0, mtimecmp_step_length, curr_pc);
    curr_pc += 4;
    store_isr_inst_code_with_pc(OP_SLLI, mcause_gpr, mcause_gpr, 0, 8, curr_pc);  // mcause_gpr = mtimecmp_step_length << 8
    curr_pc += 4;
  store_isr_inst_code_with_pc(OP_ADD, tmp_gpr, tmp_gpr, mcause_gpr, 0, curr_pc);
    curr_pc += 4;
  store_isr_inst_code_with_pc(OP_CSRRW, 0, tmp_gpr, 0, (`CSR_MTIMECMP << 5), curr_pc);
    curr_pc += 4;
    store_isr_inst_code_with_pc(OP_LD, tmp_gpr, reserve_gpr_stack, 0, tmp_gpr_stack_offset, curr_pc);  // tmp_gpr
    curr_pc += 4;
    store_isr_inst_code_with_pc(OP_LD, mcause_gpr, reserve_gpr_stack, 0, mcause_gpr_stack_offset, curr_pc);  // mcause_gpr
    curr_pc += 4;
    store_isr_inst_code_with_pc(OP_ADDI, reserve_gpr_stack, reserve_gpr_stack, 0, ori_stack_offset, curr_pc);  // restore stack pointer
    curr_pc += 4;
    next_pc = insert_random_inst_in_isr(curr_pc, 1, PRIV_LEVEL_MMODE);
    curr_pc = next_pc;
    store_isr_inst_code_with_pc(OP_MRET, 0, 0, 0, 0, curr_pc);

    tmp_gpr_stack_offset = signed'(0);     // tmp_gpr (latest_pointer - 0)
    ori_stack_offset = signed'(-8);        // original stack address (lastest_pointer - 8)

  // for S external interrupt
  curr_pc = seint_handler_pc;
    store_isr_inst_code_with_pc(OP_ADDI, reserve_gpr_stack, reserve_gpr_stack, 0, 8, curr_pc);
    curr_pc += 4;
    store_isr_inst_code_with_pc(OP_SD, 0, reserve_gpr_stack, tmp_gpr, 0, curr_pc);
    curr_pc += 4;
    store_isr_inst_code_with_pc(OP_ADDI, tmp_gpr, 0, 0, 1, curr_pc);
    curr_pc += 4;
    store_isr_inst_code_with_pc(OP_SLLI, tmp_gpr, tmp_gpr, 0, 9, curr_pc);  // seip is mip[9]
    curr_pc += 4;
    store_isr_inst_code_with_pc(OP_CSRRC, 0, tmp_gpr, 0, (`CSR_MIP << 5), curr_pc);
    curr_pc += 4;
    store_isr_inst_code_with_pc(OP_LD, tmp_gpr, reserve_gpr_stack, 0, tmp_gpr_stack_offset, curr_pc);  // tmp_gpr
    curr_pc += 4;
    store_isr_inst_code_with_pc(OP_ADDI, reserve_gpr_stack, reserve_gpr_stack, 0, ori_stack_offset, curr_pc);  // restore stack pointer
    curr_pc += 4;
    next_pc = insert_random_inst_in_isr(curr_pc, 1, PRIV_LEVEL_MMODE);
    curr_pc = next_pc;
    store_isr_inst_code_with_pc(OP_MRET, 0, 0, 0, 0, curr_pc);

  // for S timer interrupt
  curr_pc = stint_handler_pc;
    store_isr_inst_code_with_pc(OP_ADDI, reserve_gpr_stack, reserve_gpr_stack, 0, 8, curr_pc);
    curr_pc += 4;
    store_isr_inst_code_with_pc(OP_SD, 0, reserve_gpr_stack, tmp_gpr, 0, curr_pc);
    curr_pc += 4;
    store_isr_inst_code_with_pc(OP_ADDI, tmp_gpr, 0, 0, 1, curr_pc);
    curr_pc += 4;
    store_isr_inst_code_with_pc(OP_SLLI, tmp_gpr, tmp_gpr, 0, 5, curr_pc);  // stip is mip[5]
    curr_pc += 4;
    store_isr_inst_code_with_pc(OP_CSRRC, 0, tmp_gpr, 0, (`CSR_MIP << 5), curr_pc);
    curr_pc += 4;
    store_isr_inst_code_with_pc(OP_LD, tmp_gpr, reserve_gpr_stack, 0, tmp_gpr_stack_offset, curr_pc);  // tmp_gpr
    curr_pc += 4;
    store_isr_inst_code_with_pc(OP_ADDI, reserve_gpr_stack, reserve_gpr_stack, 0, ori_stack_offset, curr_pc);  // restore stack pointer
    curr_pc += 4;
    next_pc = insert_random_inst_in_isr(curr_pc, 1, PRIV_LEVEL_MMODE);
    curr_pc = next_pc;
    store_isr_inst_code_with_pc(OP_MRET, 0, 0, 0, 0, curr_pc);

  // for S software interrupt
  curr_pc = ssint_handler_pc;
    store_isr_inst_code_with_pc(OP_ADDI, reserve_gpr_stack, reserve_gpr_stack, 0, 8, curr_pc);
    curr_pc += 4;
    store_isr_inst_code_with_pc(OP_SD, 0, reserve_gpr_stack, tmp_gpr, 0, curr_pc);
    curr_pc += 4;
    store_isr_inst_code_with_pc(OP_ADDI, tmp_gpr, 0, 0, 1, curr_pc);
    curr_pc += 4;
    store_isr_inst_code_with_pc(OP_SLLI, tmp_gpr, tmp_gpr, 0, 1, curr_pc);  // ssip is mip[1]
    curr_pc += 4;
    store_isr_inst_code_with_pc(OP_CSRRC, 0, tmp_gpr, 0, (`CSR_MIP << 5), curr_pc);
    curr_pc += 4;
    store_isr_inst_code_with_pc(OP_LD, tmp_gpr, reserve_gpr_stack, 0, tmp_gpr_stack_offset, curr_pc);  // tmp_gpr
    curr_pc += 4;
    store_isr_inst_code_with_pc(OP_ADDI, reserve_gpr_stack, reserve_gpr_stack, 0, ori_stack_offset, curr_pc);  // restore stack pointer
    curr_pc += 4;
    next_pc = insert_random_inst_in_isr(curr_pc, 1, PRIV_LEVEL_MMODE);
    curr_pc = next_pc;
    store_isr_inst_code_with_pc(OP_MRET, 0, 0, 0, 0, curr_pc);
endtask

// initialize S-mode direct mode ISR() and put corresponding instruction code into memory
// NEED_CHANGE, user can decide to use this or create their own
virtual task init_smode_isr();
    bit [4:0] tmp_gpr;
    bit [4:0] scause_gpr;
    bit [63:0] curr_pc;
    bit [63:0] next_pc;
    bit [63:0] iaf_handler_pc;
    bit [63:0] intr_handler_pc;
  bit [63:0] stint_handler_pc;
  bit [63:0] ssint_handler_pc;
    bit [63:0] normal_handler_pc;
    int iaf_offset = 'h100;         // for instruction access fault handler code
    int intr_offset = 'h200;        // for interrupt handler code (S external interrupt)
  int stint_offset = 'h100;       // for S timer interrupt
  int ssint_offset = 'h200;       // for S software interrupt
    bit [31:0] imm;
    bit [31:0] tmp_gpr_stack_offset;    // offset from latest stack pointer
    bit [31:0] scause_gpr_stack_offset; // offset from latest stack pointer
    bit [31:0] ori_stack_offset;        // offset from latest stack pointer

  tmp_gpr = $urandom_range(1, 31);
    while (rsvd_gpr_arr.exists(tmp_gpr)) begin
      tmp_gpr = $urandom_range(1, 31);
    end

  scause_gpr = $urandom_range(1, 31);
    while (rsvd_gpr_arr.exists(scause_gpr) || scause_gpr == tmp_gpr) begin
      scause_gpr = $urandom_range(1, 31);
    end

    curr_pc = m_init_smode_trap_vector;

    // save context
    next_pc = insert_random_inst_in_isr(curr_pc, 0, PRIV_LEVEL_SMODE);
    curr_pc = next_pc;
    store_smode_isr_inst_code_with_pc(OP_ADDI, reserve_gpr_stack, reserve_gpr_stack, 0, 8, curr_pc);
    curr_pc += 4;
    store_smode_isr_inst_code_with_pc(OP_SD, 0, reserve_gpr_stack, tmp_gpr, 0, curr_pc);
    curr_pc += 4;
    store_smode_isr_inst_code_with_pc(OP_ADDI, reserve_gpr_stack, reserve_gpr_stack, 0, 8, curr_pc);
    curr_pc += 4;
    store_smode_isr_inst_code_with_pc(OP_SD, 0, reserve_gpr_stack, scause_gpr, 0, curr_pc);
    curr_pc += 4;

    scause_gpr_stack_offset = signed'(0);   // scause_gpr (latest_pointer - 0)
    tmp_gpr_stack_offset = signed'(-8);     // tmp_gpr (latest_pointer - 8)
    ori_stack_offset = signed'(-16);        // original stack address (lastest_pointer - 16)

    // get scause
    store_smode_isr_inst_code_with_pc(OP_CSRRS, scause_gpr, 0, 0, (`CSR_SCAUSE << 5), curr_pc);
    curr_pc += 4;

    store_smode_isr_inst_code_with_pc(OP_SLTI, tmp_gpr, scause_gpr, 0, 'hfff, curr_pc);  // scause by interrupt is 64'b1xxxxxxx
    curr_pc += 4;
    store_smode_isr_inst_code_with_pc(OP_BNE, 0, tmp_gpr, 0, intr_offset, curr_pc); // jump to curr_pc+intr_offset if it's interrupt
    intr_handler_pc = curr_pc + intr_offset;

    curr_pc += 4;
    imm = signed'(0 - `RISCV_CSR_SCAUSE_EXCODE_IACC_FAULT);
    store_smode_isr_inst_code_with_pc(OP_ADDI, tmp_gpr, scause_gpr, 0, imm, curr_pc);
    curr_pc += 4;
    store_smode_isr_inst_code_with_pc(OP_BEQ, 0, tmp_gpr, 0, iaf_offset, curr_pc); // jump to curr_pc+iaf_offset if it's instruction access fault exception
    iaf_handler_pc = curr_pc + iaf_offset;

    curr_pc += 4;
    imm = signed'(0 - `RISCV_CSR_SCAUSE_EXCODE_IPAGE_FAULT);
    store_smode_isr_inst_code_with_pc(OP_ADDI, tmp_gpr, scause_gpr, 0, imm, curr_pc);
    curr_pc += 4;
    store_smode_isr_inst_code_with_pc(OP_BEQ, 0, tmp_gpr, 0, iaf_offset-8, curr_pc); // jump to iaf_handler_pc (beq_iaf_pc+8+iaf_offset-8) if it's instruction page fault exception

    curr_pc += 4;
    normal_handler_pc = curr_pc;
    store_smode_isr_inst_code_with_pc(OP_CSRRS, tmp_gpr, 0, 0, (`CSR_SEPC << 5), curr_pc);
    curr_pc += 4;
    store_smode_isr_inst_code_with_pc(OP_ADDI, tmp_gpr, tmp_gpr, 0, 4, curr_pc);
    curr_pc += 4;
    store_smode_isr_inst_code_with_pc(OP_CSRRW, 0, tmp_gpr, 0, (`CSR_SEPC << 5), curr_pc);
    curr_pc += 4;
    store_smode_isr_inst_code_with_pc(OP_LD, tmp_gpr, reserve_gpr_stack, 0, tmp_gpr_stack_offset, curr_pc);  // tmp_gpr
    curr_pc += 4;
    store_smode_isr_inst_code_with_pc(OP_LD, scause_gpr, reserve_gpr_stack, 0, scause_gpr_stack_offset, curr_pc);  // scause_gpr
    curr_pc += 4;
    store_smode_isr_inst_code_with_pc(OP_ADDI, reserve_gpr_stack, reserve_gpr_stack, 0, ori_stack_offset, curr_pc);  // restore stack pointer
    curr_pc += 4;
    next_pc = insert_random_inst_in_isr(curr_pc, 1, PRIV_LEVEL_SMODE);
    curr_pc = next_pc;
    store_smode_isr_inst_code_with_pc(OP_SRET, 0, 0, 0, 0, curr_pc);

    // instruction access fault handler
    curr_pc = iaf_handler_pc;
    store_smode_isr_inst_code_with_pc(OP_ADD, tmp_gpr, reserve_gpr_iaf_step, reserve_gpr_iaf_offset, 0, curr_pc);
    curr_pc += 4;
    store_smode_isr_inst_code_with_pc(OP_ADDI, reserve_gpr_iaf_offset, tmp_gpr, 0, 0, curr_pc);
    curr_pc += 4;
    store_smode_isr_inst_code_with_pc(OP_ADD, tmp_gpr, tmp_gpr, reserve_gpr_boot, 0, curr_pc);
    curr_pc += 4;
    store_smode_isr_inst_code_with_pc(OP_CSRRW, 0, tmp_gpr, 0, (`CSR_SEPC << 5), curr_pc);
    curr_pc += 4;
    store_smode_isr_inst_code_with_pc(OP_LD, tmp_gpr, reserve_gpr_stack, 0, tmp_gpr_stack_offset, curr_pc);  // tmp_gpr
    curr_pc += 4;
    store_smode_isr_inst_code_with_pc(OP_LD, scause_gpr, reserve_gpr_stack, 0, scause_gpr_stack_offset, curr_pc);  // scause_gpr
    curr_pc += 4;
    store_smode_isr_inst_code_with_pc(OP_ADDI, reserve_gpr_stack, reserve_gpr_stack, 0, ori_stack_offset, curr_pc);  // restore stack pointer
    curr_pc += 4;
    next_pc = insert_random_inst_in_isr(curr_pc, 1, PRIV_LEVEL_SMODE);
    curr_pc = next_pc;
    store_smode_isr_inst_code_with_pc(OP_SRET, 0, 0, 0, 0, curr_pc);

    // interrupt handler
    curr_pc = intr_handler_pc;
  store_smode_isr_inst_code_with_pc(OP_ANDI, scause_gpr, scause_gpr, 0, 'hf, curr_pc);  // mask interrupt bit (scause[63])
    
    curr_pc += 4;
    imm = signed'(0 - `RISCV_CSR_SCAUSE_EXCODE_S_TINT);
  store_smode_isr_inst_code_with_pc(OP_ADDI, tmp_gpr, scause_gpr, 0, imm, curr_pc);
    curr_pc += 4;
  store_smode_isr_inst_code_with_pc(OP_BEQ, 0, tmp_gpr, 0, stint_offset, curr_pc);
  stint_handler_pc = curr_pc + stint_offset;

    curr_pc += 4;
    imm = signed'(0 - `RISCV_CSR_SCAUSE_EXCODE_S_SWINT);
  store_smode_isr_inst_code_with_pc(OP_ADDI, tmp_gpr, scause_gpr, 0, imm, curr_pc);
    curr_pc += 4;
  store_smode_isr_inst_code_with_pc(OP_BEQ, 0, tmp_gpr, 0, ssint_offset, curr_pc);
  ssint_handler_pc = curr_pc + ssint_offset;
    
  // for S external interrupt
    curr_pc += 4;
    store_smode_isr_inst_code_with_pc(OP_ADDI, tmp_gpr, 0, 0, 1, curr_pc);
    curr_pc += 4;
    store_smode_isr_inst_code_with_pc(OP_SLLI, tmp_gpr, tmp_gpr, 0, 9, curr_pc);  // seip is sip[9]
    curr_pc += 4;
    store_smode_isr_inst_code_with_pc(OP_CSRRC, 0, tmp_gpr, 0, (`CSR_SIP << 5), curr_pc);
    curr_pc += 4;
    store_smode_isr_inst_code_with_pc(OP_LD, tmp_gpr, reserve_gpr_stack, 0, tmp_gpr_stack_offset, curr_pc);  // tmp_gpr
    curr_pc += 4;
    store_smode_isr_inst_code_with_pc(OP_LD, scause_gpr, reserve_gpr_stack, 0, scause_gpr_stack_offset, curr_pc);  // scause_gpr
    curr_pc += 4;
    store_smode_isr_inst_code_with_pc(OP_ADDI, reserve_gpr_stack, reserve_gpr_stack, 0, ori_stack_offset, curr_pc);  // restore stack pointer
    curr_pc += 4;
    next_pc = insert_random_inst_in_isr(curr_pc, 1, PRIV_LEVEL_SMODE);
    curr_pc = next_pc;
    store_smode_isr_inst_code_with_pc(OP_SRET, 0, 0, 0, 0, curr_pc);

  // for S timer interrupt
  curr_pc = stint_handler_pc;
    store_smode_isr_inst_code_with_pc(OP_ADDI, tmp_gpr, 0, 0, 1, curr_pc);
    curr_pc += 4;
    store_smode_isr_inst_code_with_pc(OP_SLLI, tmp_gpr, tmp_gpr, 0, 5, curr_pc);  // stip is sip[5]
    curr_pc += 4;
    store_smode_isr_inst_code_with_pc(OP_CSRRC, 0, tmp_gpr, 0, (`CSR_SIP << 5), curr_pc);
    curr_pc += 4;
    store_smode_isr_inst_code_with_pc(OP_LD, tmp_gpr, reserve_gpr_stack, 0, tmp_gpr_stack_offset, curr_pc);  // tmp_gpr
    curr_pc += 4;
    store_smode_isr_inst_code_with_pc(OP_LD, scause_gpr, reserve_gpr_stack, 0, scause_gpr_stack_offset, curr_pc);  // scause_gpr
    curr_pc += 4;
    store_smode_isr_inst_code_with_pc(OP_ADDI, reserve_gpr_stack, reserve_gpr_stack, 0, ori_stack_offset, curr_pc);  // restore stack pointer
    curr_pc += 4;
    next_pc = insert_random_inst_in_isr(curr_pc, 1, PRIV_LEVEL_SMODE);
    curr_pc = next_pc;
    store_smode_isr_inst_code_with_pc(OP_SRET, 0, 0, 0, 0, curr_pc);

  // for S software interrupt
  curr_pc = ssint_handler_pc;
    store_smode_isr_inst_code_with_pc(OP_ADDI, tmp_gpr, 0, 0, 1, curr_pc);
    curr_pc += 4;
    store_smode_isr_inst_code_with_pc(OP_SLLI, tmp_gpr, tmp_gpr, 0, 1, curr_pc);  // ssip is sip[1]
    curr_pc += 4;
    store_smode_isr_inst_code_with_pc(OP_CSRRC, 0, tmp_gpr, 0, (`CSR_SIP << 5), curr_pc);
    curr_pc += 4;
    store_smode_isr_inst_code_with_pc(OP_LD, tmp_gpr, reserve_gpr_stack, 0, tmp_gpr_stack_offset, curr_pc);  // tmp_gpr
    curr_pc += 4;
    store_smode_isr_inst_code_with_pc(OP_LD, scause_gpr, reserve_gpr_stack, 0, scause_gpr_stack_offset, curr_pc);  // scause_gpr
    curr_pc += 4;
    store_smode_isr_inst_code_with_pc(OP_ADDI, reserve_gpr_stack, reserve_gpr_stack, 0, ori_stack_offset, curr_pc);  // restore stack pointer
    curr_pc += 4;
    next_pc = insert_random_inst_in_isr(curr_pc, 1, PRIV_LEVEL_SMODE);
    curr_pc = next_pc;
    store_smode_isr_inst_code_with_pc(OP_SRET, 0, 0, 0, 0, curr_pc);
endtask

// initialize S-mode vectored mode ISR() and put corresponding instruction code into memory
// NEED_CHANGE, user can decide to use this or create their own
virtual task init_smode_vectored_isr();
    bit [4:0] tmp_gpr;
    bit [4:0] scause_gpr;
    bit [63:0] curr_pc;
    bit [63:0] next_pc;
    bit [63:0] seint_handler_pc;
  bit [63:0] stint_handler_pc;
  bit [63:0] ssint_handler_pc;
  bit [63:0] expt_handler_pc;
    bit [63:0] iaf_handler_pc;
    bit [63:0] normal_handler_pc;
    int seint_offset = 'h100;       // for S external interrupt
  int stint_offset = 'h200;       // for S timer interrupt
  int ssint_offset = 'h300;       // for S software interrupt
  int expt_offset = 'h400;        // for exception
    int iaf_offset = 'h500;         // for instruction access fault handler code
    bit [31:0] imm;
    bit [31:0] tmp_gpr_stack_offset;    // offset from latest stack pointer
    bit [31:0] scause_gpr_stack_offset; // offset from latest stack pointer
    bit [31:0] ori_stack_offset;        // offset from latest stack pointer

  tmp_gpr = $urandom_range(1, 31);
    while (rsvd_gpr_arr.exists(tmp_gpr)) begin
      tmp_gpr = $urandom_range(1, 31);
    end

  scause_gpr = $urandom_range(1, 31);
    while (rsvd_gpr_arr.exists(scause_gpr) || scause_gpr == tmp_gpr) begin
      scause_gpr = $urandom_range(1, 31);
    end


    curr_pc = m_init_smode_trap_vector;
  store_smode_isr_inst_code_with_pc(OP_JAL, 0, 0, 0, expt_offset, curr_pc); // jump to curr_pc+expt_offset if it's exception
    expt_handler_pc = curr_pc + expt_offset;

  curr_pc = m_init_smode_trap_vector + 4 * `RISCV_CSR_SCAUSE_EXCODE_S_EINT;
  store_smode_isr_inst_code_with_pc(OP_JAL, 0, 0, 0, seint_offset, curr_pc); // jump to curr_pc+seint_offset if it's S external interrupt
    seint_handler_pc = curr_pc + seint_offset;

    curr_pc = m_init_smode_trap_vector + 4 * `RISCV_CSR_SCAUSE_EXCODE_S_TINT;
  store_smode_isr_inst_code_with_pc(OP_JAL, 0, 0, 0, stint_offset, curr_pc); // jump to curr_pc+stint_offset if it's S timer interrupt
    stint_handler_pc = curr_pc + stint_offset;

    curr_pc = m_init_smode_trap_vector + 4 * `RISCV_CSR_SCAUSE_EXCODE_S_SWINT;
  store_smode_isr_inst_code_with_pc(OP_JAL, 0, 0, 0, ssint_offset, curr_pc); // jump to curr_pc+ssint_offset if it's S software interrupt
    ssint_handler_pc = curr_pc + ssint_offset;

  // exception handler
    curr_pc = expt_handler_pc;

    // save context
    store_smode_isr_inst_code_with_pc(OP_ADDI, reserve_gpr_stack, reserve_gpr_stack, 0, 8, curr_pc);
    curr_pc += 4;
    store_smode_isr_inst_code_with_pc(OP_SD, 0, reserve_gpr_stack, tmp_gpr, 0, curr_pc);
    curr_pc += 4;
    store_smode_isr_inst_code_with_pc(OP_ADDI, reserve_gpr_stack, reserve_gpr_stack, 0, 8, curr_pc);
    curr_pc += 4;
    store_smode_isr_inst_code_with_pc(OP_SD, 0, reserve_gpr_stack, scause_gpr, 0, curr_pc);
    curr_pc += 4;

    scause_gpr_stack_offset = signed'(0);   // scause_gpr (latest_pointer - 0)
    tmp_gpr_stack_offset = signed'(-8);     // tmp_gpr (latest_pointer - 8)
    ori_stack_offset = signed'(-16);        // original stack address (lastest_pointer - 16)

    // get scause
    store_smode_isr_inst_code_with_pc(OP_CSRRS, scause_gpr, 0, 0, (`CSR_SCAUSE << 5), curr_pc);
    curr_pc += 4;

    imm = signed'(0 - `RISCV_CSR_SCAUSE_EXCODE_IACC_FAULT);
    store_smode_isr_inst_code_with_pc(OP_ADDI, tmp_gpr, scause_gpr, 0, imm, curr_pc);
    curr_pc += 4;
    store_smode_isr_inst_code_with_pc(OP_BEQ, 0, tmp_gpr, 0, iaf_offset, curr_pc); // jump to curr_pc+iaf_offset if it's instruction access fault exception
    iaf_handler_pc = curr_pc + iaf_offset;

    curr_pc += 4;
    imm = signed'(0 - `RISCV_CSR_SCAUSE_EXCODE_IPAGE_FAULT);
    store_smode_isr_inst_code_with_pc(OP_ADDI, tmp_gpr, scause_gpr, 0, imm, curr_pc);
    curr_pc += 4;
    store_smode_isr_inst_code_with_pc(OP_BEQ, 0, tmp_gpr, 0, iaf_offset-8, curr_pc); // jump to iaf_handler_pc (beq_iaf_pc+8+iaf_offset-8) if it's instruction page fault exception

    curr_pc += 4;
    normal_handler_pc = curr_pc;
    store_smode_isr_inst_code_with_pc(OP_CSRRS, tmp_gpr, 0, 0, (`CSR_SEPC << 5), curr_pc);
    curr_pc += 4;
    store_smode_isr_inst_code_with_pc(OP_ADDI, tmp_gpr, tmp_gpr, 0, 4, curr_pc);
    curr_pc += 4;
    store_smode_isr_inst_code_with_pc(OP_CSRRW, 0, tmp_gpr, 0, (`CSR_SEPC << 5), curr_pc);
    curr_pc += 4;
    store_smode_isr_inst_code_with_pc(OP_LD, tmp_gpr, reserve_gpr_stack, 0, tmp_gpr_stack_offset, curr_pc);  // tmp_gpr
    curr_pc += 4;
    store_smode_isr_inst_code_with_pc(OP_LD, scause_gpr, reserve_gpr_stack, 0, scause_gpr_stack_offset, curr_pc);  // scause_gpr
    curr_pc += 4;
    store_smode_isr_inst_code_with_pc(OP_ADDI, reserve_gpr_stack, reserve_gpr_stack, 0, ori_stack_offset, curr_pc);  // restore stack pointer
    curr_pc += 4;
    next_pc = insert_random_inst_in_isr(curr_pc, 1, PRIV_LEVEL_SMODE);
    curr_pc = next_pc;
    store_smode_isr_inst_code_with_pc(OP_SRET, 0, 0, 0, 0, curr_pc);

    // instruction access fault handler
    curr_pc = iaf_handler_pc;
    store_smode_isr_inst_code_with_pc(OP_ADD, tmp_gpr, reserve_gpr_iaf_step, reserve_gpr_iaf_offset, 0, curr_pc);
    curr_pc += 4;
    store_smode_isr_inst_code_with_pc(OP_ADDI, reserve_gpr_iaf_offset, tmp_gpr, 0, 0, curr_pc);
    curr_pc += 4;
    store_smode_isr_inst_code_with_pc(OP_ADD, tmp_gpr, tmp_gpr, reserve_gpr_boot, 0, curr_pc);
    curr_pc += 4;
    store_smode_isr_inst_code_with_pc(OP_CSRRW, 0, tmp_gpr, 0, (`CSR_SEPC << 5), curr_pc);
    curr_pc += 4;
    store_smode_isr_inst_code_with_pc(OP_LD, tmp_gpr, reserve_gpr_stack, 0, tmp_gpr_stack_offset, curr_pc);  // tmp_gpr
    curr_pc += 4;
    store_smode_isr_inst_code_with_pc(OP_LD, scause_gpr, reserve_gpr_stack, 0, scause_gpr_stack_offset, curr_pc);  // scause_gpr
    curr_pc += 4;
    store_smode_isr_inst_code_with_pc(OP_ADDI, reserve_gpr_stack, reserve_gpr_stack, 0, ori_stack_offset, curr_pc);  // restore stack pointer
    curr_pc += 4;
    next_pc = insert_random_inst_in_isr(curr_pc, 1, PRIV_LEVEL_SMODE);
    curr_pc = next_pc;
    store_smode_isr_inst_code_with_pc(OP_SRET, 0, 0, 0, 0, curr_pc);

    tmp_gpr_stack_offset = signed'(0);     // tmp_gpr (latest_pointer - 0)
    ori_stack_offset = signed'(-8);        // original stack address (lastest_pointer - 8)

  // S external interrupt handler
    curr_pc = seint_handler_pc;
    store_smode_isr_inst_code_with_pc(OP_ADDI, reserve_gpr_stack, reserve_gpr_stack, 0, 8, curr_pc);
    curr_pc += 4;
    store_smode_isr_inst_code_with_pc(OP_SD, 0, reserve_gpr_stack, tmp_gpr, 0, curr_pc);
    curr_pc += 4;
    store_smode_isr_inst_code_with_pc(OP_ADDI, tmp_gpr, 0, 0, 1, curr_pc);
    curr_pc += 4;
    store_smode_isr_inst_code_with_pc(OP_SLLI, tmp_gpr, tmp_gpr, 0, 9, curr_pc);  // seip is sip[9]
    curr_pc += 4;
    store_smode_isr_inst_code_with_pc(OP_CSRRC, 0, tmp_gpr, 0, (`CSR_SIP << 5), curr_pc);
    curr_pc += 4;
    store_smode_isr_inst_code_with_pc(OP_LD, tmp_gpr, reserve_gpr_stack, 0, tmp_gpr_stack_offset, curr_pc);  // tmp_gpr
    curr_pc += 4;
    store_smode_isr_inst_code_with_pc(OP_ADDI, reserve_gpr_stack, reserve_gpr_stack, 0, ori_stack_offset, curr_pc);  // restore stack pointer
    curr_pc += 4;
    next_pc = insert_random_inst_in_isr(curr_pc, 1, PRIV_LEVEL_SMODE);
    curr_pc = next_pc;
    store_smode_isr_inst_code_with_pc(OP_SRET, 0, 0, 0, 0, curr_pc);

  // for S timer interrupt
  curr_pc = stint_handler_pc;
    store_smode_isr_inst_code_with_pc(OP_ADDI, reserve_gpr_stack, reserve_gpr_stack, 0, 8, curr_pc);
    curr_pc += 4;
    store_smode_isr_inst_code_with_pc(OP_SD, 0, reserve_gpr_stack, tmp_gpr, 0, curr_pc);
    curr_pc += 4;
    store_smode_isr_inst_code_with_pc(OP_ADDI, tmp_gpr, 0, 0, 1, curr_pc);
    curr_pc += 4;
    store_smode_isr_inst_code_with_pc(OP_SLLI, tmp_gpr, tmp_gpr, 0, 5, curr_pc);  // stip is sip[5]
    curr_pc += 4;
    store_smode_isr_inst_code_with_pc(OP_CSRRC, 0, tmp_gpr, 0, (`CSR_SIP << 5), curr_pc);
    curr_pc += 4;
    store_smode_isr_inst_code_with_pc(OP_LD, tmp_gpr, reserve_gpr_stack, 0, tmp_gpr_stack_offset, curr_pc);  // tmp_gpr
    curr_pc += 4;
    store_smode_isr_inst_code_with_pc(OP_ADDI, reserve_gpr_stack, reserve_gpr_stack, 0, ori_stack_offset, curr_pc);  // restore stack pointer
    curr_pc += 4;
    next_pc = insert_random_inst_in_isr(curr_pc, 1, PRIV_LEVEL_SMODE);
    curr_pc = next_pc;
    store_smode_isr_inst_code_with_pc(OP_SRET, 0, 0, 0, 0, curr_pc);

  // for S software interrupt
  curr_pc = ssint_handler_pc;
    store_smode_isr_inst_code_with_pc(OP_ADDI, reserve_gpr_stack, reserve_gpr_stack, 0, 8, curr_pc);
    curr_pc += 4;
    store_smode_isr_inst_code_with_pc(OP_SD, 0, reserve_gpr_stack, tmp_gpr, 0, curr_pc);
    curr_pc += 4;
    store_smode_isr_inst_code_with_pc(OP_ADDI, tmp_gpr, 0, 0, 1, curr_pc);
    curr_pc += 4;
    store_smode_isr_inst_code_with_pc(OP_SLLI, tmp_gpr, tmp_gpr, 0, 1, curr_pc);  // ssip is sip[1]
    curr_pc += 4;
    store_smode_isr_inst_code_with_pc(OP_CSRRC, 0, tmp_gpr, 0, (`CSR_SIP << 5), curr_pc);
    curr_pc += 4;
    store_smode_isr_inst_code_with_pc(OP_LD, tmp_gpr, reserve_gpr_stack, 0, tmp_gpr_stack_offset, curr_pc);  // tmp_gpr
    curr_pc += 4;
    store_smode_isr_inst_code_with_pc(OP_ADDI, reserve_gpr_stack, reserve_gpr_stack, 0, ori_stack_offset, curr_pc);  // restore stack pointer
    curr_pc += 4;
    next_pc = insert_random_inst_in_isr(curr_pc, 1, PRIV_LEVEL_SMODE);
    curr_pc = next_pc;
    store_smode_isr_inst_code_with_pc(OP_SRET, 0, 0, 0, 0, curr_pc);

endtask

// NEED_CHANGE, user can decide to use this or create their own
virtual task init_mmode_isr_nest_expt();
    bit [4:0] tmp_gpr;
    bit [63:0] curr_pc;
    bit [63:0] ill_handler_pc;
    int ill_offset = 'h100;
    bit [31:0] imm;
    bit [31:0] tmp_gpr_stack_offset;    // offset from latest stack pointer
    bit [31:0] mepc_stack_offset;       // offset from latest stack pointer
    bit [31:0] mcause_stack_offset;     // offset from latest stack pointer
    bit [31:0] ori_stack_offset;        // offset from latest stack pointer

    tmp_gpr = $urandom_range(1, 31);
    while (rsvd_gpr_arr.exists(tmp_gpr)) begin
        tmp_gpr = $urandom_range(1, 31);
    end

    curr_pc = m_init_mmode_trap_vector;

    // save context
    store_isr_inst_code_with_pc(OP_ADDI, reserve_gpr_stack, reserve_gpr_stack, 0, 8, curr_pc);
    curr_pc += 4;
    store_isr_inst_code_with_pc(OP_SD, 0, reserve_gpr_stack, tmp_gpr, 0, curr_pc);
    curr_pc += 4;
    store_isr_inst_code_with_pc(OP_ADDI, reserve_gpr_stack, reserve_gpr_stack, 0, 8, curr_pc);
    curr_pc += 4;
    store_isr_inst_code_with_pc(OP_CSRRS, tmp_gpr, 0, 0, (`CSR_MEPC << 5), curr_pc);
    curr_pc += 4;
    store_isr_inst_code_with_pc(OP_SD, 0, reserve_gpr_stack, tmp_gpr, 0, curr_pc);
    curr_pc += 4;
    store_isr_inst_code_with_pc(OP_ADDI, reserve_gpr_stack, reserve_gpr_stack, 0, 8, curr_pc);
    curr_pc += 4;
    store_isr_inst_code_with_pc(OP_CSRRS, tmp_gpr, 0, 0, (`CSR_MCAUSE << 5), curr_pc);
    curr_pc += 4;
    store_isr_inst_code_with_pc(OP_SD, 0, reserve_gpr_stack, tmp_gpr, 0, curr_pc);
    curr_pc += 4;

    mcause_stack_offset = signed'(0);       // mcause (latest_pointer - 0)
    mepc_stack_offset = signed'(-8);        // mepc (latest_pointer - 8)
    tmp_gpr_stack_offset = signed'(-16);    // tmp_gpr (latest_pointer - 16)
    ori_stack_offset = signed'(-24);        // original stack address (lastest_pointer - 24)

    store_isr_inst_code_with_pc(OP_LD, tmp_gpr, reserve_gpr_stack, 0, mcause_stack_offset, curr_pc);  // mcause
    curr_pc += 4;
    imm = signed'(0 - `RISCV_CSR_MCAUSE_EXCODE_ILL);
    store_isr_inst_code_with_pc(OP_ADDI, tmp_gpr, tmp_gpr, 0, imm, curr_pc);
    curr_pc += 4;
    store_isr_inst_code_with_pc(OP_BEQ, 0, tmp_gpr, 0, ill_offset, curr_pc); // jump to curr_pc+ill_offset if it's illegal instruction exception
    ill_handler_pc = curr_pc + ill_offset;

    // other exception (could be handled by pc+4)
    curr_pc += 4;
    store_isr_inst_code_with_pc(OP_ILLEGAL, 0, 0, 0, 0, curr_pc); // insert an illegal inst
    curr_pc += 4;
    store_isr_inst_code_with_pc(OP_LD, tmp_gpr, reserve_gpr_stack, 0, mepc_stack_offset, curr_pc);  // mepc
    curr_pc += 4;
    store_isr_inst_code_with_pc(OP_ADDI, tmp_gpr, tmp_gpr, 0, 4, curr_pc);
    curr_pc += 4;
    store_isr_inst_code_with_pc(OP_CSRRW, 0, tmp_gpr, 0, (`CSR_MEPC << 5), curr_pc);
    curr_pc += 4;
    store_isr_inst_code_with_pc(OP_LD, tmp_gpr, reserve_gpr_stack, 0, tmp_gpr_stack_offset, curr_pc);  // tmp_gpr
    curr_pc += 4;
    store_isr_inst_code_with_pc(OP_ADDI, reserve_gpr_stack, reserve_gpr_stack, 0, ori_stack_offset, curr_pc);  // restore stack pointer
    curr_pc += 4;
    store_isr_inst_code_with_pc(OP_MRET, 0, 0, 0, 0, curr_pc);

    // illegal instruction exception
    curr_pc = ill_handler_pc;
    store_isr_inst_code_with_pc(OP_LD, tmp_gpr, reserve_gpr_stack, 0, mepc_stack_offset, curr_pc);  // mepc
    curr_pc += 4;
    store_isr_inst_code_with_pc(OP_ADDI, tmp_gpr, tmp_gpr, 0, 4, curr_pc);
    curr_pc += 4;
    store_isr_inst_code_with_pc(OP_CSRRW, 0, tmp_gpr, 0, (`CSR_MEPC << 5), curr_pc);
    curr_pc += 4;
    store_isr_inst_code_with_pc(OP_LD, tmp_gpr, reserve_gpr_stack, 0, tmp_gpr_stack_offset, curr_pc);  // tmp_gpr
    curr_pc += 4;
    store_isr_inst_code_with_pc(OP_ADDI, reserve_gpr_stack, reserve_gpr_stack, 0, ori_stack_offset, curr_pc);  // restore stack pointer
    curr_pc += 4;
    store_isr_inst_code_with_pc(OP_MRET, 0, 0, 0, 0, curr_pc);
endtask

// NEED_CHANGE, allocate memory region based on needs
// set address range for each memory region
virtual function void init_mem_region();
    bit [63:0] min_addr;
    bit [63:0] max_addr;
    bit [63:0] tmp;

    m_bvec_region = new();
    m_bvec_region.region_type = TYPE_BVEC;
    min_addr = init_start_pc;
    max_addr = init_start_pc + 'h2000;
    m_bvec_region.set_va_range(min_addr, max_addr);
    min_addr = min_addr + 'h1000_0000;
    max_addr = max_addr + 'h1000_0000;
    m_bvec_region.set_pa_range(min_addr, max_addr);

    m_code_region = new();
    m_code_region.region_type = TYPE_CODE;
    min_addr = init_start_pc + 'h2000 + 1;
    max_addr = min_addr + 'h10000;
    m_code_region.set_va_range(min_addr, max_addr);
    min_addr = min_addr + 'h2000_0000;
    max_addr = max_addr + 'h2000_0000;
    m_code_region.set_pa_range(min_addr, max_addr);

    m_tvec_region = new();
    m_tvec_region.region_type = TYPE_TVEC;

    // For M-mode trap vector
  min_addr = m_init_mmode_trap_vector;
    max_addr = m_init_mmode_trap_vector+'h1000;
    m_tvec_region.set_va_range(min_addr, max_addr);
    m_tvec_region.set_pa_range(min_addr, max_addr);

    // For S-mode trap vector
    min_addr = m_init_smode_trap_vector;
    max_addr = m_init_smode_trap_vector+'h1000;
    m_tvec_region.set_va_range(min_addr, max_addr);
    min_addr = min_addr + 'h3000_0000;
    max_addr = max_addr + 'h3000_0000;
    m_tvec_region.set_pa_range(min_addr, max_addr);

    m_bkdr_data_region = new();
    m_bkdr_data_region.region_type = TYPE_BKDR_DATA;
    min_addr = reserve_mem_start_va;
    max_addr = reserve_mem_start_va+'h1_0000;
    m_bkdr_data_region.set_va_range(min_addr, max_addr);
    min_addr = min_addr + 'h4000_0000;
    max_addr = max_addr + 'h4000_0000;
    m_bkdr_data_region.set_pa_range(min_addr, max_addr);

    m_stack_region = new();
    m_stack_region.region_type = TYPE_STACK;
    min_addr = stack_start_va;
    max_addr = stack_start_va+'h1_0000;
    m_stack_region.set_va_range(min_addr, max_addr);
    min_addr = min_addr + 'h6000_0000;
    max_addr = max_addr + 'h6000_0000;
    m_stack_region.set_pa_range(min_addr, max_addr);
endfunction

// This function should be overrided in child class to generate desired intruction with constraint
virtual function riscv_inst_base_txn gen_inst(bit[63:0] pc, bit gen_inst_32_en, ref bit gen_fail);
    riscv_inst_base_txn tr;

    tr = riscv_inst_base_txn::type_id::create("tr",,get_full_name());

    void'(tr.randomize());
    tr.pc = pc;

  gen_fail = 0;

    return tr;
endfunction

// Generate a fixed instruction which is from input parameter, add it to inst_arr
virtual function void gen_fixed_inst(riscv_inst_base_txn tr);
    bit [255:0] pa;

    pa = 0;
  for (int i=0; i<get_fetch_size(tr.inst_type); i++) begin
    pa[64*i+:64] = get_pa(tr.pc+i, 1, 0);
  end
    if (tr.is_in_pc_pa_queue(pa) == 0) begin
        tr.pc_pa.push_back(pa);
    end

  inst_arr[tr.pc] = tr;
endfunction

endclass: riscv_base_seq

function riscv_base_seq::new (string name = "riscv_base_seq");
    super.new(name);

  if (!$value$plusargs("MINLEN=%d", seqlen_min)) begin
    seqlen_min = 100;
  end
  if (!$value$plusargs("MAXLEN=%d", seqlen_max)) begin
    seqlen_max = 1000;
  end
  if (!$value$plusargs("START_PC=%h", init_start_pc)) begin
    init_start_pc = `RESET_PC;
  end
  if (!$value$plusargs("RESERVE_MEM_START_VA=%h", reserve_mem_start_va)) begin
    reserve_mem_start_va = `RISCV_PA_EXTMEM1_START + 'h1_0000_0000; //NEED_CHANGE
  end
  if (!$value$plusargs("STACK_START_VA=%h", stack_start_va)) begin
    stack_start_va = `RISCV_PA_EXTMEM1_START + 'h2_0000_0000; //NEED_CHANGE
  end
  if (!$value$plusargs("GPR_NUM=%d", gpr_num)) begin
    gpr_num = 32;
  end
  if (!$value$plusargs("MAX_LOOP_TIMES=%d", max_loop_times)) begin
    max_loop_times = 50;
  end
  if (!$value$plusargs("BR_RANGE=%d", br_range)) begin
    br_range = `DEFAULT_BR_RANGE;
  end
  if (!$value$plusargs("INIT_TIMECMP=%h", init_timecmp)) begin
    init_timecmp = 0;
  end
    if (!$value$plusargs("LSU_MISS_ALIGN_EN=%d", is_lsu_mis_align)) begin
        is_lsu_mis_align = 0;
    end
    if (!$value$plusargs("PRIV_LEVEL=%d", m_init_priv_level)) begin
        m_init_priv_level = PRIV_LEVEL_MMODE;
    end
    if (!$value$plusargs("TRAP_VECTOR=%h", m_init_mmode_trap_vector)) begin
        m_init_mmode_trap_vector = `RISCV_PA_EXTMEM1_START + 'hf_0000_0000;  //NEED_CHANGE
    end
    if (!$value$plusargs("SMODE_TRAP_VECTOR=%h", m_init_smode_trap_vector)) begin
        m_init_smode_trap_vector = `RISCV_PA_EXTMEM1_START + 'hff_0000_0000;  //NEED_CHANGE
    end
    if (!$value$plusargs("INTR_EN=%d", interrupt_en)) begin
        interrupt_en = 0;
    end
    if (!$value$plusargs("INTR_MUST_EN=%d", interrupt_must_en)) begin
        interrupt_must_en = 0;
    end
    if (!$value$plusargs("DIS_USMODE=%d", dis_usmode)) begin
        dis_usmode = 0;
    end
    if (!$value$plusargs("DIS_MMODE=%d", dis_mmode)) begin
        dis_mmode = 0;
    end
    if (!$value$plusargs("RANDOM_PMP_CFG=%d", random_pmp_cfg)) begin
        random_pmp_cfg = 0;
    end
    if (!$value$plusargs("NEST_EXPT_EN=%d", nest_expt_en)) begin
        nest_expt_en = 0;
    end
    if (!$value$plusargs("MTIMECMP_STEP_LENGTH=%d", mtimecmp_step_length)) begin
        mtimecmp_step_length = 'h30;
    end
    if (!$value$plusargs("MSTATUS_MPRV=%d", mstatus_mprv)) begin
        mstatus_mprv = $urandom;
    end
    if (!$value$plusargs("GEN_RVC_EN=%d", gen_rvc_en)) begin
        gen_rvc_en = 0;
    end
  if (!$value$plusargs("FPU_INST_EN=%d", fpu_inst_en)) begin
        fpu_inst_en =0;
    end
  if (!$value$plusargs("DIS_SMODE=%d", dis_smode)) begin
        dis_smode = 0;
    end
  if (!$value$plusargs("MTVEC_MODE=%d", mtvec_mode)) begin
        mtvec_mode = 0;
    end

    if (!$value$plusargs("STVEC_MODE=%d", stvec_mode)) begin
        stvec_mode = 0;
    end
    if (!$value$plusargs("TIMEOUT_SECONDS=%d", timeout_seconds)) begin
        timeout_seconds = 7200;
    end

    if (mtimecmp_step_length > 'h7ff) begin
        `uvm_fatal("fatal", $psprintf("mtimecmp_step_length can't be bigger than 'h7ff, curr_value = 0x%0x", mtimecmp_step_length));
    end

    // when enabling C-extension instruction, make below GPRs NOT in reserved GPR
    // which means it could be used for C-extension instructions
    if (gen_rvc_en == 1) begin
        rsvd_gpr_arr[1] = 1;
        rsvd_gpr_arr[2] = 1;
        rsvd_gpr_arr[8] = 1;
        rsvd_gpr_arr[9] = 1;
        rsvd_gpr_arr[10] = 1;
        rsvd_gpr_arr[11] = 1;
        rsvd_gpr_arr[12] = 1;
        rsvd_gpr_arr[13] = 1;
        rsvd_gpr_arr[14] = 1;
        rsvd_gpr_arr[15] = 1;
    end

    reserve_gpr = $urandom_range(1, 31);
    while (rsvd_gpr_arr.exists(reserve_gpr)) begin
        reserve_gpr = $urandom_range(1, 31);
    end
    rsvd_gpr_arr[reserve_gpr] = 1;

    reserve_gpr_boot = $urandom_range(1, 31);
    while (rsvd_gpr_arr.exists(reserve_gpr_boot)) begin
        reserve_gpr_boot = $urandom_range(1, 31);
    end
    rsvd_gpr_arr[reserve_gpr_boot] = 1;

    reserve_gpr_stack = $urandom_range(1, 31);
    while (rsvd_gpr_arr.exists(reserve_gpr_stack)) begin
        reserve_gpr_stack = $urandom_range(1, 31);
    end
    rsvd_gpr_arr[reserve_gpr_stack] = 1;

    reserve_gpr_iaf_step = $urandom_range(1, 31);
    while (rsvd_gpr_arr.exists(reserve_gpr_iaf_step)) begin
        reserve_gpr_iaf_step = $urandom_range(1, 31);
    end
    rsvd_gpr_arr[reserve_gpr_iaf_step] = 1;

    reserve_gpr_iaf_step_wdata = $urandom_range('h5000, 'h50000);
    if (gen_rvc_en == 0) begin
        reserve_gpr_iaf_step_wdata[1:0] = 0;
    end
    else begin
        reserve_gpr_iaf_step_wdata[0] = 0;
    end

    reserve_gpr_iaf_offset = $urandom_range(1, 31);
    while (rsvd_gpr_arr.exists(reserve_gpr_iaf_offset)) begin
        reserve_gpr_iaf_offset = $urandom_range(1, 31);
    end
    rsvd_gpr_arr[reserve_gpr_iaf_offset] = 1;

    // removes these GPRs from rsvd_gpr_arr, so that it could be used by instructions
    if (gen_rvc_en == 1) begin
        rsvd_gpr_arr.delete(1);
        rsvd_gpr_arr.delete(2);
        rsvd_gpr_arr.delete(8);
        rsvd_gpr_arr.delete(9);
        rsvd_gpr_arr.delete(10);
        rsvd_gpr_arr.delete(11);
        rsvd_gpr_arr.delete(12);
        rsvd_gpr_arr.delete(13);
        rsvd_gpr_arr.delete(14);
        rsvd_gpr_arr.delete(15);
    end

  `uvm_info("SEQ_CFG", $psprintf("seqlen_min = %0d, seqlen_max = %0d", seqlen_min, seqlen_max), UVM_NONE);
  `uvm_info("SEQ_CFG", $psprintf("reserve_mem_start_va = 0x%0x", reserve_mem_start_va), UVM_NONE);
  `uvm_info("SEQ_CFG", $psprintf("stack_start_va = 0x%0x", stack_start_va), UVM_NONE);
  `uvm_info("SEQ_CFG", $psprintf("gpr_num = %0d", gpr_num), UVM_NONE);
  `uvm_info("SEQ_CFG", $psprintf("reserve_gpr = %0d", reserve_gpr), UVM_NONE);
  `uvm_info("SEQ_CFG", $psprintf("reserve_gpr_boot = %0d", reserve_gpr_boot), UVM_NONE);
  `uvm_info("SEQ_CFG", $psprintf("reserve_gpr_stack = %0d", reserve_gpr_stack), UVM_NONE);
  `uvm_info("SEQ_CFG", $psprintf("reserve_gpr_iaf_step = %0d", reserve_gpr_iaf_step), UVM_NONE);
  `uvm_info("SEQ_CFG", $psprintf("reserve_gpr_iaf_offset = %0d", reserve_gpr_iaf_offset), UVM_NONE);
  `uvm_info("SEQ_CFG", $psprintf("is_lsu_mis_align = %0d", is_lsu_mis_align), UVM_NONE);
  `uvm_info("SEQ_CFG", $psprintf("random_pmp_cfg = %0d", random_pmp_cfg), UVM_NONE);
  `uvm_info("SEQ_CFG", $psprintf("m_init_priv_level = %0d", m_init_priv_level), UVM_NONE);
  `uvm_info("SEQ_CFG", $psprintf("m_init_mmode_trap_vector = 0x%0x", m_init_mmode_trap_vector), UVM_NONE);
  `uvm_info("SEQ_CFG", $psprintf("m_init_smode_trap_vector = 0x%0x", m_init_smode_trap_vector), UVM_NONE);
  `uvm_info("SEQ_CFG", $psprintf("rsvd_gpr_arr = %p", rsvd_gpr_arr), UVM_NONE);
  `uvm_info("SEQ_CFG", $psprintf("gen_rvc_en = %0d", gen_rvc_en), UVM_NONE);
endfunction: new

// get a random GPR wihch is not equal to reserve_gpr
function bit[4:0] riscv_base_seq::get_random_gpr();
  bit [4:0] gpr;
  bit [4:0] valid_gpr_queue[$];
  int idx;

  for (int i=0; i<gpr_queue.size(); i++) begin
      if (!rsvd_gpr_arr.exists(gpr_queue[i])) begin
      valid_gpr_queue.push_back(gpr_queue[i]);
        end
    end

  if (valid_gpr_queue.size() == 0) begin
    `uvm_fatal("fatal", $psprintf("No valid gpr found in gpr_queue"));
  end
  else begin
    idx = $urandom_range(0, valid_gpr_queue.size()-1);
    gpr = valid_gpr_queue[idx];
  end

  return gpr;
endfunction

// get a random GPR for rd
// 1. not equal to reserve_gpr
// 2. when gen_rvc_en=1, have low possibility to get 1/2/8~15 which is used by 16bit-inst, so that exception rate can be reduced
function bit[4:0] riscv_base_seq::get_random_gpr_for_rd();
  bit [4:0] gpr;
  bit [4:0] valid_gpr_queue[$];
  bit [4:0] valid_gpr_queue_1[$];
  int idx;

  for (int i=0; i<gpr_queue.size(); i++) begin
      if (!rsvd_gpr_arr.exists(gpr_queue[i])) begin
      valid_gpr_queue.push_back(gpr_queue[i]);
            if (gpr_queue[i] != 1 && gpr_queue[i] != 2 && !(gpr_queue[i] >= 8 && gpr_queue[i] <= 15)) begin
          valid_gpr_queue_1.push_back(gpr_queue[i]);
            end
        end
    end

    if (valid_gpr_queue.size() == 0) begin
    `uvm_fatal("fatal", $psprintf("No valid gpr found in gpr_queue"));
  end
    if (valid_gpr_queue_1.size() == 0 && gen_rvc_en == 1) begin
    `uvm_fatal("fatal", $psprintf("No valid gpr found in gpr_queue_1"));
  end

    if (gen_rvc_en == 0) begin
      idx = $urandom_range(0, valid_gpr_queue.size()-1);
      gpr = valid_gpr_queue[idx];
    end
    else begin
        // all GPRs can be selected
        if ($urandom % 5 == 0) begin
          idx = $urandom_range(0, valid_gpr_queue.size()-1);
          gpr = valid_gpr_queue[idx];
        end
        // only select GPRs except for 1/2/8~15 which is used by 16bit inst
        else begin
          idx = $urandom_range(0, valid_gpr_queue_1.size()-1);
          gpr = valid_gpr_queue_1[idx];
        end
    end

  return gpr;
endfunction

// get a random GPR wihch is not equal to reserve_gpr, and the GPR can't be x0
function bit[4:0] riscv_base_seq::get_random_non_zero_gpr();
  bit [4:0] gpr;
  bit [4:0] valid_gpr_queue[$];
  int idx;

  for (int i=0; i<gpr_queue.size(); i++) begin
      if (!rsvd_gpr_arr.exists(gpr_queue[i]) && gpr_queue[i] != 0) begin
      valid_gpr_queue.push_back(gpr_queue[i]);
        end
    end

  if (valid_gpr_queue.size() == 0) begin
    `uvm_fatal("fatal", $psprintf("No valid gpr found in gpr_queue"));
  end
  else begin
    idx = $urandom_range(0, valid_gpr_queue.size()-1);
    gpr = valid_gpr_queue[idx];
  end

  return gpr;
endfunction

// randomize value for 64-bit range
function bit[63:0] riscv_base_seq::random_range_64(bit[63:0] min, bit[63:0] max);
    bit [63:0] value;

    value[63:32] = $urandom_range(min[63:32], max[63:32]);
    value[31:0] = $urandom_range(min[31:0], max[31:0]);

    return value;
endfunction

function bit[63:0] riscv_base_seq::gen_fp_data(int sign=-1, int expo=-1, longint frac=-1);
  bit [63:0] fp_data;
  int expo_p;
  longint frac_p;
  int expo_bits=8;//single float
  int frac_bits=23;

  sign = sign == -1 ? $urandom %2 : sign[0];

  void'(std::randomize(rnd) with { rnd dist {0:/10, 1:/20, 2:/40, 3:/10, 4:/15, 5:/10};});
  if (rnd == 0)begin//0
    expo_p = 0;
    frac_p = 0;
  end else if(rnd == 1)begin//subnormal
    expo_p = 0;
    void'(std::randomize(frac_p) with { frac_p dist { 1 :/ 30,
                                               [2 : 2** frac_bits *1/10 -1] :/ 20,
                                               [2** frac_bits *1/10 : 2** frac_bits *5/10 -1] :/ 20,
                                               [2** frac_bits *5/10 : 2** frac_bits *9/10 -1] :/ 20,
                                               [2** frac_bits *9/10 : 2** frac_bits -2] :/ 20,
                                               (2** frac_bits -1) :/10};});
  end else if(rnd == 2)begin//normal
    void'(std::randomize(expo_p) with { expo_p dist { 1 :/ 30, 
                                               [157 : 160] :/ 5, // 32-bit int
                                               [189 : 192] :/ 5, // 64-bit int
                                               [2 : 2** expo_bits *1/10 -1] :/ 20,
                                               [2** expo_bits *1/10 : 2** expo_bits *5/10 -1] :/ 20,
                                               [2** expo_bits *5/10 : 2** expo_bits *9/10 -1] :/ 20,
                                               [2** expo_bits *9/10 : 2** expo_bits -3] :/ 20,
                                               (2** expo_bits -2) :/10};});
    void'(std::randomize(frac_p) with { frac_p dist { 0 :/ 30,
                                               [1 : 2** frac_bits *1/10 -1] :/ 20,
                                               [2** frac_bits *1/10 : 2** frac_bits *5/10 -1] :/ 20,
                                               [2** frac_bits *5/10 : 2** frac_bits *9/10 -1] :/ 20,
                                               [2** frac_bits *9/10 : 2** frac_bits -2] :/ 20,
                                               (2** frac_bits -1) :/10};});
  end else if(rnd == 3)begin//infinite
    expo_p = 2** expo_bits -1;
    frac_p = 0;
  end else if(rnd == 4)begin//SNaN
    expo_p = 2** expo_bits -1;
    frac_bits -=1;
    void'(std::randomize(frac_p) with { frac_p dist { 1 :/ 20,
                                               [2 : 2** frac_bits *1/10 -1] :/ 20,
                                               [2** frac_bits *1/10 : 2** frac_bits *5/10 -1] :/ 20,
                                               [2** frac_bits *5/10 : 2** frac_bits *9/10 -1] :/ 20,
                                               [2** frac_bits *9/10 : 2** frac_bits -2] :/ 20,
                                               (2** frac_bits -1) :/20};});
    frac_bits +=1;
  end else begin//QNaN
    expo_p = 2** expo_bits -1;
    frac_bits -=1;
    void'(std::randomize(frac_p) with { frac_p dist { 0 :/ 30,
                                               [1 : 2** frac_bits *1/10 -1] :/ 20,
                                               [2** frac_bits *1/10 : 2** frac_bits *5/10 -1] :/ 20,
                                               [2** frac_bits *5/10 : 2** frac_bits *9/10 -1] :/ 20,
                                               [2** frac_bits *9/10 : 2** frac_bits -2] :/ 20,
                                               (2** frac_bits -1) :/10};});

    frac_p += 1<< frac_bits;
    frac_bits +=1;
  end

  expo = expo == -1 ? expo_p : expo & ~(-1<< expo_bits);
  frac = frac == -1 ? frac_p : frac & ~(-1<< frac_bits);

  fp_data[63:32] = $urandom;//single float data
  fp_data[31:0]  = (sign << (expo_bits + frac_bits)) + (expo << frac_bits) + frac;

  return fp_data;

endfunction

function bit[63:0] riscv_base_seq::fp_data_delta(bit[63:0] fp_data_i);
  bit [63:0] fp_data;
  int sign, expo;
  longint frac;
  int expo_bits=8;//single float
  int frac_bits=23;

  void'(std::randomize(rnd2));
  void'(std::randomize(rnd) with { rnd dist {0:/10, 1:/10, 2:/10, 3:/10, 4:/30, 5:/30};});

    sign = 0;
    expo = 0;
    frac = 0;
  if (rnd == 0)begin
    sign = rnd2[16] ;
  end else if(rnd == 1)begin
    expo = rnd2[15:14] << (expo_bits -2);
  end else if(rnd == 2)begin
    expo = rnd2[9:8];
  end else if(rnd == 3)begin
    frac = rnd2[7:4] << (frac_bits -4);
  end else if(rnd == 4)begin
    frac = rnd2[3:0];
  end else begin
    sign = rnd2[16] ;
    expo = rnd2[15:14] << (expo_bits -2);
    expo += rnd2[9:8];
    frac = rnd2[7:4] << (frac_bits -4);
    frac += rnd2[3:0];
  end


  fp_data[63:32] = $urandom;//single float data
  fp_data[31:0]  = $urandom % 50 ==0 ? $urandom : (sign << (expo_bits + frac_bits)) + (expo << frac_bits) + frac;

  fp_data ^= fp_data_i;

  return fp_data;

endfunction

// return 1 if it's load instruction, return 0 if it's store instruction
function bit riscv_base_seq::is_load_inst(inst_type_e inst_type);
  if (inst_type == OP_LB || inst_type == OP_LH || inst_type == OP_LW || inst_type == OP_LBU || inst_type == OP_LHU || inst_type == OP_LWU || inst_type == OP_LD || inst_type == OP_FLW || inst_type == OP_C_LWSP || inst_type == OP_C_LDSP || inst_type == OP_C_LW || inst_type == OP_C_LD) begin
    return 1;
  end
  else if (inst_type == OP_SB || inst_type == OP_SH || inst_type == OP_SW || inst_type == OP_SD || inst_type == OP_FSW || inst_type == OP_C_SWSP || inst_type == OP_C_SDSP || inst_type == OP_C_SW || inst_type == OP_C_SD) begin
    return 0;
  end
  else begin
    `uvm_fatal("fatal", $psprintf("Should only check LSU instruction for is_load_inst(), current input inst_type = 0x%0x", inst_type));
  end
endfunction

// return 1 if it's branch instruction, return 0 if it's NOT branch instruction
function bit riscv_base_seq::is_branch_inst(inst_type_e inst_type);
  if (inst_type == OP_JAL || inst_type == OP_JALR || inst_type == OP_BEQ || inst_type == OP_BNE || inst_type == OP_BLT || inst_type == OP_BGE || inst_type == OP_BLTU || inst_type ==OP_BGEU  || inst_type == OP_C_J || inst_type == OP_C_JR || inst_type == OP_C_JALR || inst_type == OP_C_BEQZ || inst_type == OP_C_BNEZ) begin
    return 1;
  end
  else begin
    return 0;
  end
endfunction

function bit[63:0] riscv_base_seq::get_field_value(bit[63:0] reg_value, int idx_high, int idx_low);
    bit [63:0] field_value;
    bit [63:0] field_mask;

    field_mask = 0;
    for (int i=0; i<=(idx_high-idx_low); i++) begin
        field_mask += 1 << i;
    end

    field_value = (reg_value >> idx_low) & field_mask;

    return field_value;
endfunction

// For CSRRW/CSRRS/CSRRC, src is rs1; For CSRRWI/CSRRSI/CSRRCI, src is zimm
// return if has exception
function bit riscv_base_seq::cal_csr(inst_type_e inst_type, bit[11:0] csr, bit[4:0] src, bit[4:0] rd);
    bit [63:0] tmp64;
    bit [63:0] zimm64;
    bit [4:0] rs1;
    bit [63:0] original_field_value;
    bit has_exception = 0;
    csr_register csr_reg;

    has_exception = check_csr_exception(inst_type, csr, src, rd);

    if (has_exception == 0) begin
        csr_reg = get_csr_reg(csr);
        tmp64 = csr_reg.reg_value;
        zimm64 = src;
        rs1 = src;

        for (int i=0; i<csr_reg.field_queue.size(); i++) begin
            original_field_value = csr_reg.field_queue[i].field_value;

            if (inst_type == OP_CSRRW) begin
                csr_reg.field_queue[i].field_value = get_field_value(m_gpr[rs1], csr_reg.field_queue[i].idx_high, csr_reg.field_queue[i].idx_low);
            end
            else if (inst_type == OP_CSRRS) begin
                for (int j=csr_reg.field_queue[i].idx_low; j<=csr_reg.field_queue[i].idx_high; j++) begin
                    if (m_gpr[rs1][j] == 1) begin
                        csr_reg.field_queue[i].field_value[j-csr_reg.field_queue[i].idx_low] = 1;
                    end
                end
            end
            else if (inst_type == OP_CSRRC) begin
                for (int j=csr_reg.field_queue[i].idx_low; j<=csr_reg.field_queue[i].idx_high; j++) begin
                    if (m_gpr[rs1][j] == 1) begin
                        csr_reg.field_queue[i].field_value[j-csr_reg.field_queue[i].idx_low] = 0;
                    end
                end
            end
            else if (inst_type == OP_CSRRWI) begin
                csr_reg.field_queue[i].field_value = get_field_value(zimm64, csr_reg.field_queue[i].idx_high, csr_reg.field_queue[i].idx_low);
            end
            else if (inst_type == OP_CSRRSI) begin
                for (int j=csr_reg.field_queue[i].idx_low; j<=csr_reg.field_queue[i].idx_high; j++) begin
                    if (zimm64[j] == 1) begin
                        csr_reg.field_queue[i].field_value[j-csr_reg.field_queue[i].idx_low] = 1;
                    end
                end
            end
            else if (inst_type == OP_CSRRCI) begin
                for (int j=csr_reg.field_queue[i].idx_low; j<=csr_reg.field_queue[i].idx_high; j++) begin
                    if (zimm64[j] == 1) begin
                        csr_reg.field_queue[i].field_value[j-csr_reg.field_queue[i].idx_low] = 0;
                    end
                end
            end
            else begin
                `uvm_fatal("fatal", $psprintf("non-CSR instruction 0x%0x in cal_csr()", inst_type));
            end

            if (csr_reg.field_queue[i].is_ignore_value() == 1) begin
                // restore current field for ignored value
                csr_reg.field_queue[i].field_value = original_field_value;
            end
        end

        m_gpr[rd] = tmp64;
        get_csr_field(csr, csr_reg);
    end

    return has_exception;
endfunction

// get real csr write data
function bit[63:0] riscv_base_seq::get_csr_wdata(inst_type_e inst_type, bit[4:0] src, bit[63:0] ori_value);
    bit [63:0] csr_wdata;

    if (inst_type == OP_CSRRW) begin
        csr_wdata = m_gpr[src];
    end
    else if (inst_type == OP_CSRRS) begin
        csr_wdata = ori_value;
        for (int i=0; i<64; i++) begin
            if (m_gpr[src][i] == 1) begin
                csr_wdata[i] = 1;
            end
        end
    end
    else if (inst_type == OP_CSRRC) begin
        csr_wdata = ori_value;
        for (int i=0; i<64; i++) begin
            if (m_gpr[src][i] == 1) begin
                csr_wdata[i] = 0;
            end
        end
    end
    else if (inst_type == OP_CSRRWI) begin
        csr_wdata = src;
    end
    else if (inst_type == OP_CSRRSI) begin
        csr_wdata = ori_value;
        for (int i=0; i<5; i++) begin
            if (src[i] == 1) begin
                csr_wdata[i] = 1;
            end
        end
    end
    else if (inst_type == OP_CSRRCI) begin
        csr_wdata = ori_value;
        for (int i=0; i<5; i++) begin
            if (src[i] == 1) begin
                csr_wdata[i] = 0;
            end
        end
    end

    return csr_wdata;
endfunction

// check if there is exception for csr instruction
// NEED_CHANGE, update according to actual supported CSR
function bit riscv_base_seq::check_csr_exception(inst_type_e inst_type, bit[11:0] csr, bit[4:0] src, bit[4:0] rd);
    bit has_exception = 0;
    bit [63:0] csr_wdata;
    bit [63:0] ori_value;
    bit [63:0] src_data;
    int hpmcounter_idx;
    bit [63:0] inv_va;
    bit [63:0] mcause_int_base = 1 << 63;
    bit [63:0] mcause_expt_base = 0;
    bit [63:0] scause_int_base = 1 << 63;
    bit [63:0] scause_expt_base = 0;

    if (inst_type == OP_CSRRW || inst_type == OP_CSRRS || inst_type == OP_CSRRC) begin
        src_data = m_gpr[src];
    end
    else begin
        src_data = src;
    end

    // wrong privilege access check and legal csr check
    if (!(
          // M-mode CSRs
          (csr == `CSR_MVENDORID) ||
          (csr == `CSR_MARCHID) ||
          (csr == `CSR_MIMPID) ||
          (csr == `CSR_MHARTID) ||
          (csr == `CSR_MSTATUS) ||
          (csr == `CSR_MISA) ||
          (csr == `CSR_MEDELEG) ||
          (csr == `CSR_MIDELEG) ||
          (csr == `CSR_MIE) ||
          (csr == `CSR_MTVEC) ||
          (csr == `CSR_MCOUNTEREN) ||
          (csr >= `CSR_MHPMEVENT3 && csr <= `CSR_MHPMEVENT31) ||
          (csr == `CSR_MSCRATCH) ||
          (csr == `CSR_MEPC) ||
          (csr == `CSR_MCAUSE) ||
          (csr == `CSR_MTVAL) ||
          (csr == `CSR_MIP) ||
          (csr == `CSR_PMPCFG0) ||
          (csr == `CSR_PMPCFG2) ||
          (csr >= `CSR_PMPADDR0 && csr <= `CSR_PMPADDR15) ||
          (csr == `CSR_MCYCLE) ||
          (csr == `CSR_MINSTRET) ||
          (csr >= `CSR_MHPMCOUNTER3 && csr <= `CSR_MHPMCOUNTER31) ||
          (csr == `CSR_TSELECT) ||
          (csr == `CSR_TDATA1) ||
          (csr == `CSR_TDATA2) ||
          (csr == `CSR_DCSR) ||
          (csr == `CSR_MTIMECMP) ||
          // S-mode CSRs
          (csr == `CSR_SSTATUS) ||
          (csr == `CSR_SIE) ||
          (csr == `CSR_STVEC) ||
          (csr == `CSR_SCOUNTEREN) ||
          (csr == `CSR_SSCRATCH) ||
          (csr == `CSR_SEPC) ||
          (csr == `CSR_SCAUSE) ||
          (csr == `CSR_STVAL) ||
          (csr == `CSR_SIP) ||
          (csr == `CSR_SATP) ||
          // U-mode CSRs
          (csr == `CSR_FFLAGS) ||
          (csr == `CSR_FRM) ||
          (csr == `CSR_FCSR) ||
          (csr == `CSR_CYCLE) ||
          (csr == `CSR_TIME) ||
          (csr == `CSR_INSTRET) ||
          (csr >= `CSR_HPMCOUNTER3 && csr <= `CSR_HPMCOUNTER31)
         )) begin
        has_exception = 1;
    end
    else if ((
              // M-mode CSRs
              (csr == `CSR_MVENDORID) ||
              (csr == `CSR_MARCHID) ||
              (csr == `CSR_MIMPID) ||
              (csr == `CSR_MHARTID) ||
              (csr == `CSR_MSTATUS) ||
              (csr == `CSR_MISA) ||
              (csr == `CSR_MEDELEG) ||
              (csr == `CSR_MIDELEG) ||
              (csr == `CSR_MIE) ||
              (csr == `CSR_MTVEC) ||
              (csr == `CSR_MCOUNTEREN) ||
              (csr >= `CSR_MHPMEVENT3 && csr <= `CSR_MHPMEVENT31) ||
              (csr == `CSR_MSCRATCH) ||
              (csr == `CSR_MEPC) ||
              (csr == `CSR_MCAUSE) ||
              (csr == `CSR_MTVAL) ||
              (csr == `CSR_MIP) ||
              (csr == `CSR_PMPCFG0) ||
              (csr == `CSR_PMPCFG2) ||
              (csr >= `CSR_PMPADDR0 && csr <= `CSR_PMPADDR15) ||
              (csr == `CSR_MCYCLE) ||
              (csr == `CSR_MINSTRET) ||
              (csr >= `CSR_MHPMCOUNTER3 && csr <= `CSR_MHPMCOUNTER31) ||
              (csr == `CSR_TSELECT) ||
              (csr == `CSR_TDATA1) ||
              (csr == `CSR_TDATA2) ||
              (csr == `CSR_DCSR) ||
              (csr == `CSR_MTIMECMP)
             )
             && (m_curr_priv_level == PRIV_LEVEL_SMODE || m_curr_priv_level == PRIV_LEVEL_UMODE)) begin
        has_exception = 1;
    end
    else if ((
              // M-mode CSRs
              (csr == `CSR_MVENDORID) ||
              (csr == `CSR_MARCHID) ||
              (csr == `CSR_MIMPID) ||
              (csr == `CSR_MHARTID) ||
              (csr == `CSR_MSTATUS) ||
              (csr == `CSR_MISA) ||
              (csr == `CSR_MEDELEG) ||
              (csr == `CSR_MIDELEG) ||
              (csr == `CSR_MIE) ||
              (csr == `CSR_MTVEC) ||
              (csr == `CSR_MCOUNTEREN) ||
              (csr >= `CSR_MHPMEVENT3 && csr <= `CSR_MHPMEVENT31) ||
              (csr == `CSR_MSCRATCH) ||
              (csr == `CSR_MEPC) ||
              (csr == `CSR_MCAUSE) ||
              (csr == `CSR_MTVAL) ||
              (csr == `CSR_MIP) ||
              (csr == `CSR_PMPCFG0) ||
              (csr == `CSR_PMPCFG2) ||
              (csr >= `CSR_PMPADDR0 && csr <= `CSR_PMPADDR15) ||
              (csr == `CSR_MCYCLE) ||
              (csr == `CSR_MINSTRET) ||
              (csr >= `CSR_MHPMCOUNTER3 && csr <= `CSR_MHPMCOUNTER31) ||
              (csr == `CSR_TSELECT) ||
              (csr == `CSR_TDATA1) ||
              (csr == `CSR_TDATA2) ||
              (csr == `CSR_DCSR) ||
              (csr == `CSR_MTIMECMP) ||
              // S-mode CSRs
              (csr == `CSR_SSTATUS) ||
              (csr == `CSR_SIE) ||
              (csr == `CSR_STVEC) ||
              (csr == `CSR_SCOUNTEREN) ||
              (csr == `CSR_SSCRATCH) ||
              (csr == `CSR_SEPC) ||
              (csr == `CSR_SCAUSE) ||
              (csr == `CSR_STVAL) ||
              (csr == `CSR_SIP) ||
              (csr == `CSR_SATP)
             )
             && (m_curr_priv_level == PRIV_LEVEL_UMODE)) begin
        has_exception = 1;
    end

    // mcounteren/scounteren check
    if (mcounteren[0] == 0 && csr == `CSR_CYCLE && m_curr_priv_level != PRIV_LEVEL_MMODE) begin
        has_exception = 1;
    end
    else if (mcounteren[1] == 0 && csr == `CSR_TIME && m_curr_priv_level != PRIV_LEVEL_MMODE) begin
        has_exception = 1;
    end
    else if (mcounteren[2] == 0 && csr == `CSR_INSTRET && m_curr_priv_level != PRIV_LEVEL_MMODE) begin
        has_exception = 1;
    end
    else if ((mcounteren[0] == 0 || scounteren[0] == 0) && csr == `CSR_CYCLE && m_curr_priv_level == PRIV_LEVEL_UMODE) begin
        has_exception = 1;
    end
    else if ((mcounteren[1] == 0 || scounteren[1] == 0) && csr == `CSR_TIME && m_curr_priv_level == PRIV_LEVEL_UMODE) begin
        has_exception = 1;
    end
    else if ((mcounteren[2] == 0 || scounteren[2] == 0) && csr == `CSR_INSTRET && m_curr_priv_level == PRIV_LEVEL_UMODE) begin
        has_exception = 1;
    end
    else if (csr >= `CSR_HPMCOUNTER3 && csr <= `CSR_HPMCOUNTER31) begin
        hpmcounter_idx = csr - `CSR_HPMCOUNTER3 + 3;
        if (mcounteren[hpmcounter_idx] == 0 && m_curr_priv_level != PRIV_LEVEL_MMODE) begin
            has_exception = 1;
        end
        else if ((mcounteren[hpmcounter_idx] == 0 || scounteren[hpmcounter_idx] == 0) && m_curr_priv_level == PRIV_LEVEL_UMODE) begin
            has_exception = 1;
        end
    end

    // mstatus WLRL check
    if (csr == `CSR_MSTATUS) begin
        ori_value[`RISCV_CSR_MSTATUS_MPP] = mpp;
        csr_wdata = get_csr_wdata(inst_type, src, ori_value);
        if (csr_wdata[`RISCV_CSR_MSTATUS_MPP] == 2) begin
            has_exception = 1;
        end
    end

    // mcause/scause WLRL check
    if (csr == `CSR_MCAUSE) begin
        ori_value = mcause;
        csr_wdata = get_csr_wdata(inst_type, src, ori_value);
        if (csr_wdata != mcause_int_base + `RISCV_CSR_MCAUSE_EXCODE_S_SWINT &&
            csr_wdata != mcause_int_base + `RISCV_CSR_MCAUSE_EXCODE_M_SWINT &&
            csr_wdata != mcause_int_base + `RISCV_CSR_MCAUSE_EXCODE_S_TINT &&
            csr_wdata != mcause_int_base + `RISCV_CSR_MCAUSE_EXCODE_M_TINT &&
            csr_wdata != mcause_int_base + `RISCV_CSR_MCAUSE_EXCODE_S_EINT &&
            csr_wdata != mcause_int_base + `RISCV_CSR_MCAUSE_EXCODE_M_EINT &&
            csr_wdata != mcause_expt_base + `RISCV_CSR_MCAUSE_EXCODE_IAMA &&
            csr_wdata != mcause_expt_base + `RISCV_CSR_MCAUSE_EXCODE_IACC_FAULT &&
            csr_wdata != mcause_expt_base + `RISCV_CSR_MCAUSE_EXCODE_ILL &&
            csr_wdata != mcause_expt_base + `RISCV_CSR_MCAUSE_EXCODE_BKPT &&
            csr_wdata != mcause_expt_base + `RISCV_CSR_MCAUSE_EXCODE_LAMA &&
            csr_wdata != mcause_expt_base + `RISCV_CSR_MCAUSE_EXCODE_LACC_FAULT &&
            csr_wdata != mcause_expt_base + `RISCV_CSR_MCAUSE_EXCODE_SAMA &&
            csr_wdata != mcause_expt_base + `RISCV_CSR_MCAUSE_EXCODE_SACC_FAULT &&
            csr_wdata != mcause_expt_base + `RISCV_CSR_MCAUSE_EXCODE_UCALL &&
            csr_wdata != mcause_expt_base + `RISCV_CSR_MCAUSE_EXCODE_SCALL &&
            csr_wdata != mcause_expt_base + `RISCV_CSR_MCAUSE_EXCODE_MCALL &&
            csr_wdata != mcause_expt_base + `RISCV_CSR_MCAUSE_EXCODE_IPAGE_FAULT &&
            csr_wdata != mcause_expt_base + `RISCV_CSR_MCAUSE_EXCODE_LPAGE_FAULT &&
            csr_wdata != mcause_expt_base + `RISCV_CSR_MCAUSE_EXCODE_SPAGE_FAULT) begin
            has_exception = 1;
        end
    end
    else if (csr == `CSR_SCAUSE) begin
        ori_value = scause;
        csr_wdata = get_csr_wdata(inst_type, src, ori_value);
        if (csr_wdata != scause_int_base + `RISCV_CSR_SCAUSE_EXCODE_S_SWINT &&
            csr_wdata != scause_int_base + `RISCV_CSR_SCAUSE_EXCODE_S_TINT &&
            csr_wdata != scause_int_base + `RISCV_CSR_SCAUSE_EXCODE_S_EINT &&
            csr_wdata != scause_expt_base + `RISCV_CSR_SCAUSE_EXCODE_IAMA &&
            csr_wdata != scause_expt_base + `RISCV_CSR_SCAUSE_EXCODE_IACC_FAULT &&
            csr_wdata != scause_expt_base + `RISCV_CSR_SCAUSE_EXCODE_ILL &&
            csr_wdata != scause_expt_base + `RISCV_CSR_SCAUSE_EXCODE_BKPT &&
            csr_wdata != scause_expt_base + `RISCV_CSR_SCAUSE_EXCODE_LAMA &&
            csr_wdata != scause_expt_base + `RISCV_CSR_SCAUSE_EXCODE_LACC_FAULT &&
            csr_wdata != scause_expt_base + `RISCV_CSR_SCAUSE_EXCODE_SAMA &&
            csr_wdata != scause_expt_base + `RISCV_CSR_SCAUSE_EXCODE_SACC_FAULT &&
            csr_wdata != scause_expt_base + `RISCV_CSR_SCAUSE_EXCODE_UCALL &&
            csr_wdata != scause_expt_base + `RISCV_CSR_SCAUSE_EXCODE_SCALL &&
            csr_wdata != scause_expt_base + `RISCV_CSR_SCAUSE_EXCODE_IPAGE_FAULT &&
            csr_wdata != scause_expt_base + `RISCV_CSR_SCAUSE_EXCODE_LPAGE_FAULT &&
            csr_wdata != scause_expt_base + `RISCV_CSR_SCAUSE_EXCODE_SPAGE_FAULT) begin
            has_exception = 1;
        end
    end

    // write RO CSR check
    if (!((inst_type == OP_CSRRS || inst_type == OP_CSRRC || inst_type == OP_CSRRSI || inst_type == OP_CSRRCI) && (src_data == 0))) begin
        if (csr == `CSR_MVENDORID ||
            csr == `CSR_MARCHID ||
            csr == `CSR_MIMPID ||
            csr == `CSR_MHARTID ||
            csr == `CSR_CYCLE ||
            csr == `CSR_TIME ||
            csr == `CSR_INSTRET ||
            (csr >= `CSR_HPMCOUNTER3 && csr <= `CSR_HPMCOUNTER31)) begin
            has_exception = 1;
        end
    end

    // tvm check
    if (tvm == 1 && csr == `CSR_SATP && m_curr_priv_level == PRIV_LEVEL_SMODE) begin
        has_exception = 1;
    end

    return has_exception;
endfunction

// NEED_CHANGE, update according to actual supported CSR
function csr_register riscv_base_seq::get_csr_reg(bit[11:0] csr);
    csr_register csr_reg = new();

    if (csr == `CSR_MEPC) begin
        csr_reg.set_field(mepc[63:1], 63, 1);
    end
    if (csr == `CSR_SEPC) begin
        csr_reg.set_field(sepc[63:1], 63, 1);
    end
    else if (csr == `CSR_MTVEC) begin
        csr_reg.set_field(m_curr_mmode_trap_vector[63:2], 63, 2);
    end
    else if (csr == `CSR_STVEC) begin
        csr_reg.set_field(m_curr_smode_trap_vector[63:2], 63, 2);
    end
    else if (csr == `CSR_MSCRATCH) begin
        csr_reg.set_field(mscratch, 63, 0);
    end
    else if (csr == `CSR_SSCRATCH) begin
        csr_reg.set_field(sscratch, 63, 0);
    end
    else if (csr == `CSR_MCOUNTEREN) begin
        csr_reg.set_field(mcounteren, 63, 0);
    end
    else if (csr == `CSR_SCOUNTEREN) begin
        csr_reg.set_field(scounteren, 63, 0);
    end
    else if (csr == `CSR_MTIMECMP) begin
        csr_reg.set_field(mtimecmp, 63, 0);
    end
    else if (csr == `CSR_MCAUSE) begin
        csr_reg.set_field(mcause, 63, 0);
    end
    else if (csr == `CSR_SCAUSE) begin
        csr_reg.set_field(scause, 63, 0);
    end
    else if (csr == `CSR_MEDELEG) begin
        csr_reg.set_field(medeleg, 63, 0);
    end
    else if (csr == `CSR_MIDELEG) begin
        csr_reg.set_field(mideleg, 63, 0);
    end
    else if (csr == `CSR_MINSTRET) begin
        csr_reg.set_field(minstret, 63, 0);
    end
    else if (csr == `CSR_MSTATUS) begin
        csr_reg.set_field(tsr, 22, 22);
        csr_reg.set_field(tw, 21, 21);
        csr_reg.set_field(tvm, 20, 20);
        csr_reg.set_field(mxr, 19, 19);
        csr_reg.set_field(mprv, 17, 17);

        csr_reg.set_field(mpp, 12, 11);
        csr_reg.set_field_illegal_value(2);

        csr_reg.set_field(spp, 8, 8);
        csr_reg.set_field(mpie, 7, 7);
        csr_reg.set_field(spie, 5, 5);
        csr_reg.set_field(mie, 3, 3);
        csr_reg.set_field(sie, 1, 1);
    end
    else if (csr == `CSR_SSTATUS) begin
        csr_reg.set_field(mxr, 19, 19);
        csr_reg.set_field(spp, 8, 8);
        csr_reg.set_field(spie, 5, 5);
        csr_reg.set_field(sie, 1, 1);
    end
    else if (csr == `CSR_SATP) begin
        csr_reg.set_field(satp_mode, 63, 60);
        for (int i=0; i<16; i++) begin
            if (i != 'h0 && i != 'hf) begin
                csr_reg.set_field_ignore_value(i);
            end
        end
    end

    csr_reg.cal_reg_value();

    return csr_reg;
endfunction

// NEED_CHANGE, update according to actual supported CSR
function void riscv_base_seq::get_csr_field(bit[11:0] csr, csr_register csr_reg);
    if (csr == `CSR_MEPC) begin
        mepc[63:1] = csr_reg.field_queue[0].field_value;
    end
    if (csr == `CSR_SEPC) begin
        sepc[63:1] = csr_reg.field_queue[0].field_value;
    end
    else if (csr == `CSR_MTVEC) begin
        m_curr_mmode_trap_vector[63:2] = csr_reg.field_queue[0].field_value;
    end
    else if (csr == `CSR_STVEC) begin
        m_curr_smode_trap_vector[63:2] = csr_reg.field_queue[0].field_value;
    end
    else if (csr == `CSR_MSCRATCH) begin
        mscratch = csr_reg.field_queue[0].field_value;
    end
    else if (csr == `CSR_SSCRATCH) begin
        sscratch = csr_reg.field_queue[0].field_value;
    end
    else if (csr == `CSR_MCOUNTEREN) begin
        mcounteren = csr_reg.field_queue[0].field_value;
        mcounteren[`RISCV_CSR_MCOUNTEREN_RS0] = 0;
    end
    else if (csr == `CSR_SCOUNTEREN) begin
        scounteren = csr_reg.field_queue[0].field_value;
        scounteren[`RISCV_CSR_SCOUNTEREN_RS0] = 0;
    end
    else if (csr == `CSR_MTIMECMP) begin
        mtimecmp = csr_reg.field_queue[0].field_value;
    end
    else if (csr == `CSR_MCAUSE) begin
        mcause = csr_reg.field_queue[0].field_value;
    end
    else if (csr == `CSR_SCAUSE) begin
        scause = csr_reg.field_queue[0].field_value;
    end
    else if (csr == `CSR_MEDELEG) begin
        medeleg = csr_reg.field_queue[0].field_value;
        medeleg[`RISCV_CSR_MEDELEG_WPRI3] = 0;
        medeleg[`RISCV_CSR_MEDELEG_WPRI2] = 0;
        medeleg[`RISCV_CSR_MEDELEG_WPRI1] = 0;
        medeleg[`RISCV_CSR_MEDELEG_WPRI0] = 0;
    end
    else if (csr == `CSR_MIDELEG) begin
        mideleg = csr_reg.field_queue[0].field_value;
        mideleg[`RISCV_CSR_MIDELEG_WPRI2] = 0;
        mideleg[`RISCV_CSR_MIDELEG_WPRI1] = 0;
        mideleg[`RISCV_CSR_MIDELEG_WPRI0] = 0;
        mideleg[`RISCV_CSR_MIDELEG_UEID] = 0;
        mideleg[`RISCV_CSR_MIDELEG_UTID] = 0;
        mideleg[`RISCV_CSR_MIDELEG_USID] = 0;
    end
    else if (csr == `CSR_MINSTRET) begin
        minstret = csr_reg.field_queue[0].field_value;
    end
    else if (csr == `CSR_MSTATUS) begin
        tsr = csr_reg.field_queue[0].field_value;
        tw = csr_reg.field_queue[1].field_value;
        tvm = csr_reg.field_queue[2].field_value;
        mxr = csr_reg.field_queue[3].field_value;
        mprv = csr_reg.field_queue[4].field_value;
        mpp = csr_reg.field_queue[5].field_value;
        spp = csr_reg.field_queue[6].field_value;
        mpie = csr_reg.field_queue[7].field_value;
        spie = csr_reg.field_queue[8].field_value;
        mie = csr_reg.field_queue[9].field_value;
        sie = csr_reg.field_queue[10].field_value;
    end
    else if (csr == `CSR_SSTATUS) begin
        mxr = csr_reg.field_queue[0].field_value;
        spp = csr_reg.field_queue[1].field_value;
        spie = csr_reg.field_queue[2].field_value;
        sie = csr_reg.field_queue[3].field_value;
    end
    else if (csr == `CSR_SATP) begin
        satp_mode = csr_reg.field_queue[0].field_value;
    end
endfunction

// set default value for CSRs
function void riscv_base_seq::init_csr();
    m_curr_mmode_trap_vector = 0;
    m_curr_smode_trap_vector = 0;
    mepc = 0;
    sepc = 0;
    m_curr_priv_level = PRIV_LEVEL_MMODE;
    mie = 0;
    sie = 0;
    mpie = 0;
    spie = 0;
    mpp = 0;
    spp = 0;
    mprv = 0;
    mxr = 0;
    tsr = 0;
    tw = 0;
    tvm = 0;
    satp_mode = 0;
    mscratch = 0;
    sscratch = 0;
    mcounteren = 0;
    scounteren = 0;
    mtimecmp = 'hffff_ffff_ffff_ffff;
    mcause = 0;
    scause = 0;
    cause = 0;
    medeleg = 0;
    mideleg = 0;
    minstret = 0;
endfunction


// check if single memory region is valid
// return 0 if valid, return 1 if not
function bit riscv_base_seq::check_single_region_validity(mem_region region);
    if (region == null) begin
        return 0;
    end

    if (region.va_range.size() != region.pa_range.size()) begin
        `uvm_info("debug", $psprintf("va range size 0x%0x is not equal to pa range size 0x%0x", region.va_range.size(), region.pa_range.size()), UVM_NONE);
        return 1;
    end
    else begin
        for (int i=0; i<region.va_range.size(); i++) begin
            if (region.va_range[i].min_addr > region.va_range[i].max_addr) begin
                `uvm_info("debug", $psprintf("For va range %0d, min_addr(0x%0x) > max_addr(0x%0x)", i, region.va_range[i].min_addr, region.va_range[i].max_addr), UVM_NONE);
                return 1;
            end
            if (region.pa_range[i].min_addr > region.pa_range[i].max_addr) begin
                `uvm_info("debug", $psprintf("For pa range %0d, min_addr(0x%0x) > max_addr(0x%0x)", i, region.pa_range[i].min_addr, region.pa_range[i].max_addr), UVM_NONE);
                return 1;
            end
            if ((region.va_range[i].max_addr - region.va_range[i].min_addr) != (region.pa_range[i].max_addr - region.pa_range[i].min_addr)) begin
                `uvm_info("debug", $psprintf("For range %0d, va size 0x%0x is not equal to pa size 0x%0x", i, (region.va_range[i].max_addr - region.va_range[i].min_addr), (region.pa_range[i].max_addr - region.pa_range[i].min_addr)), UVM_NONE);
                return 1;
            end

            // check va range is not overlap with other range
            for (int j=0; j<region.va_range.size(); j++) begin
                if (j != i) begin
                    if (region.va_range[j].is_addr_in_range(region.va_range[i].min_addr) == 1 || region.va_range[j].is_addr_in_range(region.va_range[i].max_addr) == 1) begin
                        `uvm_info("debug", $psprintf("there is overlap for va range %0d(0x%0x ~ 0x%0x) and range %0d(0x%0x ~ 0x%0x)", i, region.va_range[i].min_addr, region.va_range[i].max_addr, j, region.va_range[j].min_addr, region.va_range[j].max_addr), UVM_NONE);
                        return 1;
                    end
                end
            end

            // check pa range is not overlap with other range
            for (int j=0; j<region.pa_range.size(); j++) begin
                if (j != i) begin
                    if (region.pa_range[j].is_addr_in_range(region.pa_range[i].min_addr) == 1 || region.pa_range[j].is_addr_in_range(region.pa_range[i].max_addr) == 1) begin
                        `uvm_info("debug", $psprintf("there is overlap for pa range %0d(0x%0x ~ 0x%0x) and range %0d(0x%0x ~ 0x%0x)", i, region.pa_range[i].min_addr, region.pa_range[i].max_addr, j, region.pa_range[j].min_addr, region.pa_range[j].max_addr), UVM_NONE);
                        return 1;
                    end
                end
            end
        end
    end

    return 0;
endfunction

// check if all memory region is valid
// return 0 if valid, return 1 if not
function bit riscv_base_seq::check_all_region_validity();
    mem_region region_queue[$];

    if (check_single_region_validity(m_code_region) == 1) begin
        `uvm_info("debug", "code region is not valid", UVM_NONE);
        return 1;
    end
    if (check_single_region_validity(m_bvec_region) == 1) begin
        `uvm_info("debug", "boot vector region is not valid", UVM_NONE);
        return 1;
    end
    if (check_single_region_validity(m_tvec_region) == 1) begin
        `uvm_info("debug", "trap vector region is not valid", UVM_NONE);
        return 1;
    end
    if (check_single_region_validity(m_bkdr_data_region) == 1) begin
        `uvm_info("debug", "backdoor data region is not valid", UVM_NONE);
        return 1;
    end
    if (check_single_region_validity(m_stack_region) == 1) begin
        `uvm_info("debug", "stack region is not valid", UVM_NONE);
        return 1;
    end
    if (check_single_region_validity(m_data_region) == 1) begin
        `uvm_info("debug", "data region is not valid", UVM_NONE);
        return 1;
    end

    region_queue.push_back(m_code_region);
    region_queue.push_back(m_bvec_region);
    region_queue.push_back(m_tvec_region);
    region_queue.push_back(m_bkdr_data_region);
    region_queue.push_back(m_stack_region);
    if (m_data_region != null) begin
        region_queue.push_back(m_data_region);
    end

    for (int i=0; i<region_queue.size(); i++) begin
        for (int j=0; j<region_queue[i].va_range.size(); j++) begin
            // check va range address overlap
            for (int k=0; k<region_queue.size(); k++) begin
                if (i != k) begin
                    if (region_queue[k].is_addr_in_va_range(region_queue[i].va_range[j].min_addr) == 1 || region_queue[k].is_addr_in_va_range(region_queue[i].va_range[j].max_addr) == 1) begin
                        `uvm_info("debug", $psprintf("region %0d and region %0d has overlap for va range %0d(0x%0x ~ 0x%0x)", i, k, j, region_queue[i].va_range[j].min_addr, region_queue[i].va_range[j].max_addr), UVM_NONE);
                        return 1;
                    end
                end
            end

            // check pa range address overlap
            for (int k=0; k<region_queue.size(); k++) begin
                if (i != k) begin
                    if (region_queue[k].is_addr_in_pa_range(region_queue[i].pa_range[j].min_addr) == 1 || region_queue[k].is_addr_in_pa_range(region_queue[i].pa_range[j].max_addr) == 1) begin
                        `uvm_info("debug", $psprintf("region %0d and region %0d has overlap for pa range %0d(0x%0x ~ 0x%0x)", i, k, j, region_queue[i].pa_range[j].min_addr, region_queue[i].pa_range[j].max_addr), UVM_NONE);
                        return 1;
                    end
                end
            end
        end
    end

    return 0;
endfunction

// store instruction bin code into memory
function void riscv_base_seq::store_inst_code(riscv_inst_base_txn tr);
    void'(tr.gen_inst_bin_code());

    for (int j=0; j<tr.pc_pa.size(); j++) begin
        for (int i=0; i<tr.inst_bin_code_size; i++) begin
            riscv_mem::dut_mem[tr.pc_pa[j][64*i+:64]] = tr.inst_bin_code[8*i+:8];
            riscv_mem::rm_mem[tr.pc_pa[j][64*i+:64]] = tr.inst_bin_code[8*i+:8];
            m_init_mem[tr.pc_pa[j][64*i+:64]] = tr.inst_bin_code[8*i+:8];
            m_mem[tr.pc_pa[j][64*i+:64]] = tr.inst_bin_code[8*i+:8];
            `uvm_info("debug", $psprintf("store_inst_code(%0d), addr = 0x%0x, data = 0x%0x", j, tr.pc_pa[j][64*i+:64], tr.inst_bin_code[8*i+:8]), UVM_DEBUG);
        end
    end
endfunction

function int riscv_base_seq::get_st_bytes(inst_type_e inst_type);
    if (inst_type == OP_SB) begin
        return 1;
    end
    else if (inst_type == OP_SH) begin
        return 2;
    end
    else if (inst_type == OP_SW || inst_type == OP_C_SWSP || inst_type == OP_C_SW || inst_type == OP_FSW) begin
        return 4;
    end
    else if (inst_type == OP_SD || inst_type == OP_C_SDSP || inst_type == OP_C_SD) begin
        return 8;
    end
    else begin
        `uvm_fatal("fatal", $psprintf("inst_type should be store inst, but got 0x%0x", inst_type));
    end
endfunction

// check if input address range is overlap with input pc instruction code address range
function bit riscv_base_seq::is_overlap_with_inst_code(bit[63:0] pa, int bytes, int code_size, bit[255:0] pc_pa[$]);
    bit [63:0] code_addr;

    for (int i=0; i<pc_pa.size(); i++) begin
    for (int j=0; j<code_size; j++) begin
      code_addr = pc_pa[i][64*j+:64];
            if (code_addr >= pa && code_addr <= pa+bytes-1) begin
                return 1;
            end
        end
    end

    return 0;
endfunction

// check if input address range is overlap with existing pc in inst_arr[]
// return 1 if found and update target pc of input ref param
function bit riscv_base_seq::is_overlap_with_exist_pc(bit[63:0] addr, int bytes, bit is_fetch, ref bit[63:0] pc[$]);
    bit [63:0] loop_pc;
    bit [63:0] pa;

    if (check_mem_trans_access_violation(addr, bytes, is_fetch, 0) == 1) begin
        return 0;
    end
    else begin
        pa = va2pa(addr, is_fetch);
    end

    if (inst_arr.first(loop_pc))
    do begin
        if (is_overlap_with_inst_code(pa, bytes, inst_arr[loop_pc].inst_bin_code_size, inst_arr[loop_pc].pc_pa) == 1) begin
            pc.push_back(loop_pc);
        end
    end while (inst_arr.next(loop_pc));

    if (pc.size() == 0) begin
        return 0;
    end
    else begin
        return 1;
    end
endfunction

function bit[63:0] riscv_base_seq::insert_random_inst_in_isr(bit[63:0] pc, bit is_exit_trap, privilege_level_e mode);
    riscv_inst_base_txn txn;
    bit has_big_branch = 0;
    bit [63:0] next_pc;
    int sfence_weight;

    txn = riscv_inst_base_txn::type_id::create("txn",,get_full_name());

    if (mode == PRIV_LEVEL_MMODE) begin
        sfence_weight = 1;
    end
    else begin  // S-mode
        if (tvm == 1) begin
            sfence_weight = 0;
        end
        else begin
            sfence_weight = 1;
        end
    end

    void'(txn.randomize() with {
        inst_type dist {['h0:'h1d]:/1, ['h30:'h3c]:/1, 'h20:/1, ['h22:'h27]:/1, ['h40:'h4a]:/1, ['h50:'h55]:/1, 'h60:/1, 'h61:/1, 'h67:/sfence_weight};
        inst_type != 'h71;
        inst_type != 'h111;
        inst_type != 'h112;
        rd == 0;
    });

    if (txn.inst_type >= 'h20 && txn.inst_type <= 'h27) begin
        if (is_exit_trap == 1) begin
            txn.imm = 4;
        end
        else begin
            if ($urandom % 4 == 0) begin
                txn.imm = 4;
            end
            else begin
                txn.imm = $urandom_range('hb00, 'hfff);
                txn.imm[1:0] = 0;
                has_big_branch = 1;
            end
        end
    end
    else if (txn.inst_type >= 'h110 && txn.inst_type <= 'h114) begin
        txn.imm = 4;
    end
    else if (txn.inst_type >= 'h40 && txn.inst_type <= 'h4a || txn.inst_type >= 'h70 && txn.inst_type <= 'h71 || txn.inst_type >= 'h104 && txn.inst_type <= 'h107) begin
        txn.rs1 = reserve_gpr_stack;
        txn.imm = 8;
    end
    else if (txn.inst_type >= 'h50 && txn.inst_type <= 'h55) begin
        if (mode == PRIV_LEVEL_MMODE) begin
        if (txn.inst_type == OP_CSRRS || txn.inst_type == OP_CSRRC) begin  // for coverage
          txn.rs1 = 0;
          if ($urandom % 7 == 0) begin
            txn.imm[16:5] = `CSR_MIP;
          end
          else if ($urandom % 7 == 1) begin
            txn.imm[16:5] = `CSR_MTVAL;
          end
          else if ($urandom % 7 == 2) begin
            txn.imm[16:5] = `CSR_MCAUSE;
          end
          else if ($urandom % 7 == 3) begin
            txn.imm[16:5] = `CSR_MEPC;
          end
          else if ($urandom % 7 == 4) begin
            txn.imm[16:5] = `CSR_MTVEC;
          end
          else if ($urandom % 7 == 5) begin
            txn.imm[16:5] = `CSR_MIE;
          end
          else begin
            txn.imm[16:5] = `CSR_MSTATUS;
          end
        end
        else begin
        // NEED_CHANGE, replace with a useless CSR (can be written with random value)
        txn.imm[16:5] = `CSR_MSCRATCH2;
        end
        end
        else begin
      // NEED_CHANGE, replace with a useless CSR (can be written with random value)
        txn.imm[16:5] = `CSR_SSCRATCH2;
        end
    end

    if (mode == PRIV_LEVEL_MMODE) begin
        store_isr_inst_code_with_pc(txn.inst_type, txn.rd, txn.rs1, txn.rs2, txn.imm, pc);
    end
    else begin
        store_smode_isr_inst_code_with_pc(txn.inst_type, txn.rd, txn.rs1, txn.rs2, txn.imm, pc);
    end

    if (has_big_branch == 1) begin
        if (mode == PRIV_LEVEL_MMODE) begin
            trap_pc_offset = txn.imm - 4;
        end
        else begin
            trap_pc_offset_smode = txn.imm - 4;
        end
    end

    if (txn.inst_type > OP_ILLEGAL) begin
        next_pc = pc + 2;
    end
    else begin
        next_pc = pc + 4;
    end

    return next_pc;
endfunction

// get system time (seconds since 1970/1/1)
function int riscv_base_seq::get_system_time();
  int curr_system_seconds;
  int fh;

  // call "date" and put seconds since 1970/1/1 into temp file "localtime"
  void'($system("date +%s > localtime"));

  fh = $fopen("localtime", "r");

  void'($fscanf(fh, "%d", curr_system_seconds));

  $fclose(fh);

  // delete temp file
  void'($system("rm localtime"));

  return curr_system_seconds;
endfunction

// get a not-yet-configured pmp entry id
function bit[31:0] riscv_base_seq::get_pmp_id(ref pmpcfg_cfg pmp_cfg);
    bit [31:0] pmp_id;
    bit [31:0] idx_queue[$];
    int idx;
    int has_found=0;
    pmpcfg_cfg  pmpcfg_cfg_txn ;

    for (int i=0; i<`MAX_PMP_NUM; i++) begin
        if (!m_used_pmp_idx.exists(i)) begin
            idx_queue.push_back(i);
        end
    end

    if (idx_queue.size() == 0) begin
        `uvm_fatal("fatal", $psprintf("no avaiable pmp idx"));
    end
    else begin
        if(pmp_cfg.a != `PMP_TOR) begin
            idx = $urandom_range(0, idx_queue.size()-1);
            pmp_id = idx_queue[idx];
            m_used_pmp_idx[pmp_id] = 1;
        end
        else begin
            //NATOR mode
            foreach(idx_queue[i]) begin
                if( (idx_queue[i]==0) && (!m_used_pmp_idx.exists(idx_queue[i]))  ) begin
                    m_used_pmp_idx[idx_queue[i]  ] = 1;
                    pmp_id                         = idx_queue[i];
                    has_found                      = 1;
                    break;
                end
                else if((idx_queue[i]!=0) && (!m_used_pmp_idx.exists(idx_queue[i])) &&  (!m_used_pmp_idx.exists(idx_queue[i]-1)) ) begin
                    m_used_pmp_idx[idx_queue[i]  ] = 1;
                    m_used_pmp_idx[idx_queue[i]-1] = 1;
                    pmp_id                         = idx_queue[i];
                    has_found                      = 1;
                    pmpcfg_cfg_txn  = new();
                    pmpcfg_cfg_txn.r=1;
                    pmpcfg_cfg_txn.w=1;
                    pmpcfg_cfg_txn.x=1;
                    pmpcfg_cfg_txn.s=0;
                    pmpcfg_cfg_txn.a=0;
                    pmpcfg_cfg_txn.l=0;
                    void'(pmpcfg_cfg_txn.pack_cfg());
                    m_init_pmpcfg_cfg[idx_queue[i]-1]  = pmpcfg_cfg_txn;

                    break;
                end
            end
            if(has_found == 0) begin
                idx = $urandom_range(0, idx_queue.size()-1);
                pmp_id = idx_queue[idx]   ;
                m_used_pmp_idx[pmp_id] = 1;
                pmp_cfg.a = `PMP_NAPOT    ;
            end
        end
    end
    return pmp_id;

endfunction

function void riscv_base_seq::set_pmp_region(bit[63:0] region_start, bit[63:0] region_end);
    pmpaddr_cfg pmpaddr_cfg_txn, pmpaddr_cfg_txn_1;
    pmpcfg_cfg  pmpcfg_cfg_txn ;
    int idx;
    pmpaddr_cfg_txn = new();
    pmpaddr_cfg_txn_1= new();
    pmpcfg_cfg_txn  = new();

    void'(pmpcfg_cfg_txn.randomize() with{
        r == 1;
        w == 1;
        x == 1;
        a inside {`PMP_TOR, `PMP_NAPOT};
        s inside {[0:3]};
        l inside {0, 1};
    });
    idx = get_pmp_id(pmpcfg_cfg_txn);
    void'(pmpcfg_cfg_txn.pack_cfg());

    pmpaddr_cfg_txn.min_addr = region_start ;
    pmpaddr_cfg_txn.max_addr = region_end   ;
    pmpaddr_cfg_txn.cal_addr(pmpcfg_cfg_txn.a);

    if((pmpcfg_cfg_txn.a == `PMP_TOR) && (idx!=0)) begin
        pmpaddr_cfg_txn_1.min_addr=0;
        pmpaddr_cfg_txn_1.max_addr=0;
        pmpaddr_cfg_txn_1.paddr = (pmpaddr_cfg_txn.min_addr>>2);
        m_init_pmpaddr_cfg[idx-1] = pmpaddr_cfg_txn_1;
    end


    m_init_pmpaddr_cfg[idx] = pmpaddr_cfg_txn;
    m_init_pmpcfg_cfg[idx]  = pmpcfg_cfg_txn;
endfunction

function bit riscv_base_seq::is_in_boot_pc_range(bit[63:0] pc);
    bit [63:0] loop_pc;

    if (m_boot_pc.first(loop_pc))
    do begin
    for (int i=0; i<inst_arr[loop_pc].inst_bin_code_size; i++) begin
      if (pc == loop_pc + i) begin
              return 1;
          end
    end
    end while (m_boot_pc.next(loop_pc));

    return 0;
endfunction

function bit riscv_base_seq::is_in_tvec_pc_range(bit[63:0] pc);
    bit [63:0] loop_pc;

    if (m_tvec_pc.first(loop_pc))
    do begin
    for (int i=0; i<inst_arr[loop_pc].inst_bin_code_size; i++) begin
      if (pc == loop_pc + i) begin
              return 1;
          end
    end
    end while (m_tvec_pc.next(loop_pc));

    return 0;
endfunction

function void riscv_base_seq::gen_gpr_queue();
  bit [63:0] rand_val;
  bit found_same_value;
    int idx;
  
  if(gpr_num + rsvd_gpr_arr.size() > 32)  gpr_num = 32 - rsvd_gpr_arr.size();
  `uvm_info("SEQ_CFG", $psprintf("gpr_num = %0d", gpr_num), UVM_NONE);

    gpr_queue = new[gpr_num];

  for (int i=0; i<gpr_num; i++) begin
    // when gpr_num == 1, don't use gpr0
    if (gpr_num == 1) begin
      rand_val = ($urandom() % 31) + 1;
    end
    else begin
      rand_val = $urandom() % 32;
    end

    found_same_value = 0;
        if (rsvd_gpr_arr.exists(rand_val)) begin
            found_same_value = 1;
        end
        else begin
        for (int j=0; j<i; j++) begin
          if (rand_val == gpr_queue[j]) begin
            found_same_value = 1;
            break;
          end
        end
        end

    if (found_same_value == 0) begin
      gpr_queue[i] = rand_val;
    end
    else begin
      i--;
    end
  end
  
  for (int i=0; i<gpr_num; i++) begin
    `uvm_info("debug", $psprintf("gpr_queue[%0d] = %0d", i, gpr_queue[i]), UVM_HIGH);
  end

endfunction

function void riscv_base_seq::gen_fpr_queue(int cnt);
  randc32 fpr_idx;
  
    void'(std::randomize(rnd) with { rnd dist {1:/5, [2:4]:/40, 5:/10, [6:10]:/5, [11:21]:/5, [22:31]:/30, 32:/5};});
    if(cnt != -1) rnd = cnt;
    fpr_queue = new[rnd];

     // TODO: Steve Richmond (SiLabs) says: "Xcelium won't take the unique inside
     //       of a constraint block in a scoped randomize call.  So I just recoded
     //       as foreach's to get it through".
     // Discuss with Neo Fang
     //void'(std::randomize(fpr_queue) with { unique {fpr_queue};});
     void'(std::randomize(fpr_queue) with {
       foreach (fpr_queue[i]) {
         foreach (fpr_queue[j]) {
           (i != j) -> (fpr_queue[i] != fpr_queue[j]);
         }
       }
     });
  
    for(int i=0; i<rnd; i++)begin
    `uvm_info("debug", $psprintf("fpr_queue[%0d] = %0d", i, fpr_queue[i]), UVM_NONE);
  end
endfunction

// get sign extended value
function bit[63:0] riscv_base_seq::sign_extend (bit[63:0] data, int size);
  bit [63:0] result;

  // negative, need sign-extend
  if (data[size-1] == 1) begin
    result = data;
    for (int i=size; i<64; i++) begin
      result += (1 << i);
    end
  end
  // positive, return original value
  else begin
    result = data;
  end

  return result;
endfunction

function bit[63:0] riscv_base_seq::m_load(bit[63:0] addr, int ld_byte, bit is_sext);
  bit [63:0] result;
    bit [63:0] va;

  result = 0;
  for (int i=0; i<ld_byte; i++) begin
        if (!m_mem.exists(addr+i)) begin
            m_mem[addr+i] = $urandom;
            m_init_mem[addr+i] = m_mem[addr+i];
            riscv_mem::dut_mem[addr+i] = m_mem[addr+i];
            riscv_mem::rm_mem[addr+i] = m_mem[addr+i];
        end
        accessed_lsu_pa_arr[addr+i] = 1;
    result += m_mem[addr+i] << (i*8);
  end

  if (is_sext == 1) begin
    result = sign_extend(result, ld_byte*8);
  end

  return result;
endfunction

function void riscv_base_seq::m_store(bit[63:0] addr, bit [63:0] data, int st_byte);
    bit [63:0] va;

  for (int i=0; i<st_byte; i++) begin
    m_mem[addr+i] = (data >> (8*i)) & 8'hff;
        accessed_lsu_pa_arr[addr+i] = 1;
  end
endfunction

// calculate various instructions, get result pc and result gpr
// If ctype == RETURN_PC, return next pc and update m_gpr[]
// If ctype == RETURN_GPR, return result gpr and don't update m_gpr[]
function bit[63:0] riscv_base_seq::calculate_op(inst_type_e inst_type, bit[63:0] cpc, bit[4:0] rd, bit[4:0] rs1, bit[4:0] rs2, bit[31:0] imm, cal_op_type_e ctype);
  bit[63:0] rpc;
  bit[63:0] tmp64;
  bit[63:0] simm64;
  bit[63:0] addr;
  bit[127:0] tmp128_0;
  bit[127:0] tmp128_1;
  bit[127:0] tmp128_2;
    bit has_exception;
  int code_size;

  // calculate return pc
  code_size = get_fetch_size(inst_type);
  rpc = cpc + code_size;

    has_exception = 0;

  // use this trick to not really update m_gpr[] since m_gpr[0] will be overrided at the end of function
  if (ctype == RETURN_GPR) begin
    rd = 0;
  end

    if (check_fetch_fault_exception(cpc, code_size) == 1) begin
        has_exception = 1;
        if (check_page_fault_violation(cpc, code_size, 1, 0) == 1) begin
            cause = `RISCV_CSR_MCAUSE_EXCODE_IPAGE_FAULT;
        end
        else begin
            cause = `RISCV_CSR_MCAUSE_EXCODE_IACC_FAULT;
        end
    end
  else if (inst_type == OP_ILLEGAL || inst_type == OP_C_ILLEGAL) begin
        has_exception = 1;
        cause = `RISCV_CSR_MCAUSE_EXCODE_ILL;
    end
    else if (inst_type == OP_LUI) begin
    m_gpr[rd] = sign_extend((imm[31:12] << 12), 32);
  end
  else if (inst_type == OP_AUIPC) begin
    m_gpr[rd] = cpc + sign_extend((imm[31:12] << 12), 32);
  end
  else if (inst_type == OP_ADDI) begin
    m_gpr[rd] = m_gpr[rs1] + sign_extend(imm[11:0], 12);
  end
  else if (inst_type == OP_SLTI) begin
    if (signed'(m_gpr[rs1]) < signed'(sign_extend(imm[11:0], 12))) begin
      m_gpr[rd] = 1;
    end
    else begin
      m_gpr[rd] = 0;
    end
  end
  else if (inst_type == OP_SLTIU) begin
    if (m_gpr[rs1] < sign_extend(imm[11:0], 12)) begin
      m_gpr[rd] = 1;
    end
    else begin
      m_gpr[rd] = 0;
    end
  end
  else if (inst_type == OP_XORI) begin
    m_gpr[rd] = m_gpr[rs1] ^ sign_extend(imm[11:0], 12);
  end
  else if (inst_type == OP_ORI) begin
    m_gpr[rd] = m_gpr[rs1] | sign_extend(imm[11:0], 12);
  end
  else if (inst_type == OP_ANDI) begin
    m_gpr[rd] = m_gpr[rs1] & sign_extend(imm[11:0], 12);
  end
  else if (inst_type == OP_SLLI) begin
    m_gpr[rd] = m_gpr[rs1] << imm[5:0];
  end
  else if (inst_type == OP_SRLI) begin
    m_gpr[rd] = m_gpr[rs1] >> imm[5:0];
  end
  else if (inst_type == OP_SRAI) begin
    m_gpr[rd] = sign_extend((m_gpr[rs1] >> imm[5:0]), (64 - imm[5:0]));
  end
  else if (inst_type == OP_ADD) begin
    m_gpr[rd] = m_gpr[rs1] + m_gpr[rs2];
  end
  else if (inst_type == OP_SUB) begin
    m_gpr[rd] = m_gpr[rs1] - m_gpr[rs2];
  end
  else if (inst_type == OP_SLL) begin
    m_gpr[rd] = m_gpr[rs1] << m_gpr[rs2][5:0];
  end
  else if (inst_type == OP_SLT) begin
    if (signed'(m_gpr[rs1]) < signed'(m_gpr[rs2])) begin
      m_gpr[rd] = 1;
    end
    else begin
      m_gpr[rd] = 0;
    end
  end
  else if (inst_type == OP_SLTU) begin
    if (m_gpr[rs1] < m_gpr[rs2]) begin
      m_gpr[rd] = 1;
    end
    else begin
      m_gpr[rd] = 0;
    end
  end
  else if (inst_type == OP_XOR) begin
    m_gpr[rd] = m_gpr[rs1] ^ m_gpr[rs2];
  end
  else if (inst_type == OP_SRL) begin
    m_gpr[rd] = m_gpr[rs1] >> m_gpr[rs2][5:0];
  end
  else if (inst_type == OP_SRA) begin
    m_gpr[rd] = sign_extend((m_gpr[rs1] >> m_gpr[rs2][5:0]), (64 - m_gpr[rs2][5:0]));
  end
  else if (inst_type == OP_OR) begin
    m_gpr[rd] = m_gpr[rs1] | m_gpr[rs2];
  end
  else if (inst_type == OP_AND) begin
    m_gpr[rd] = m_gpr[rs1] & m_gpr[rs2];
  end
  else if (inst_type == OP_ADDIW) begin
    simm64 = sign_extend(imm[11:0], 12);
    tmp64 = m_gpr[rs1][31:0] + simm64[31:0];
    m_gpr[rd] = sign_extend(tmp64[31:0], 32);
  end
  else if (inst_type == OP_SLLIW) begin
    tmp64 = m_gpr[rs1][31:0] << imm[4:0];
    m_gpr[rd] = sign_extend(tmp64[31:0], 32);
  end
  else if (inst_type == OP_SRLIW) begin
    tmp64 = m_gpr[rs1][31:0] >> imm[4:0];
    m_gpr[rd] = sign_extend(tmp64[31:0], 32);
  end
  else if (inst_type == OP_SRAIW) begin
    tmp64 = sign_extend((m_gpr[rs1][31:0] >> imm[4:0]), (32 - imm[4:0]));
    m_gpr[rd] = sign_extend(tmp64[31:0], 32);
  end
  else if (inst_type == OP_ADDW) begin
    tmp64 = m_gpr[rs1][31:0] + m_gpr[rs2][31:0];
    m_gpr[rd] = sign_extend(tmp64[31:0], 32);
  end
  else if (inst_type == OP_SUBW) begin
    tmp64 = m_gpr[rs1][31:0] - m_gpr[rs2][31:0];
    m_gpr[rd] = sign_extend(tmp64[31:0], 32);
  end
  else if (inst_type == OP_SLLW) begin
    tmp64 = m_gpr[rs1][31:0] << m_gpr[rs2][4:0];
    m_gpr[rd] = sign_extend(tmp64[31:0], 32);
  end
  else if (inst_type == OP_SRLW) begin
    tmp64 = m_gpr[rs1][31:0] >> m_gpr[rs2][4:0];
    m_gpr[rd] = sign_extend(tmp64[31:0], 32);
  end
  else if (inst_type == OP_SRAW) begin
    tmp64 = sign_extend((m_gpr[rs1][31:0] >> m_gpr[rs2][4:0]), (32 - m_gpr[rs2][4:0]));
    m_gpr[rd] = sign_extend(tmp64[31:0], 32);
  end
  else if (inst_type == OP_JAL) begin
    rpc = cpc + sign_extend((imm[20:1] << 1), 21);
        if (rpc % 2 != 0) begin
            has_exception = 1;
            cause = `RISCV_CSR_MCAUSE_EXCODE_IAMA;
        end
        else begin
        m_gpr[rd] = cpc + 4;
        end
  end
  else if (inst_type == OP_JALR) begin
    rpc = m_gpr[rs1] + sign_extend(imm[11:0], 12);
    rpc = rpc & 'hffff_ffff_ffff_fffe;
        if (rpc % 2 != 0) begin
            has_exception = 1;
            cause = `RISCV_CSR_MCAUSE_EXCODE_IAMA;
        end
        else begin
        m_gpr[rd] = cpc + 4;
        end
  end
  else if (inst_type == OP_BEQ) begin
    if (m_gpr[rs1] == m_gpr[rs2]) begin
      rpc = cpc + sign_extend((imm[12:1] << 1), 13);
    end
        if (rpc % 2 != 0) begin
            has_exception = 1;
            cause = `RISCV_CSR_MCAUSE_EXCODE_IAMA;
        end
  end
  else if (inst_type == OP_BNE) begin
    if (m_gpr[rs1] != m_gpr[rs2]) begin
      rpc = cpc + sign_extend((imm[12:1] << 1), 13);
    end
        if (rpc % 2 != 0) begin
            has_exception = 1;
            cause = `RISCV_CSR_MCAUSE_EXCODE_IAMA;
        end
  end
  else if (inst_type == OP_BLT) begin
    if (signed'(m_gpr[rs1]) < signed'(m_gpr[rs2])) begin
      rpc = cpc + sign_extend((imm[12:1] << 1), 13);
    end
        if (rpc % 2 != 0) begin
            has_exception = 1;
            cause = `RISCV_CSR_MCAUSE_EXCODE_IAMA;
        end
  end
  else if (inst_type == OP_BGE) begin
    if (signed'(m_gpr[rs1]) >= signed'(m_gpr[rs2])) begin
      rpc = cpc + sign_extend((imm[12:1] << 1), 13);
    end
        if (rpc % 2 != 0) begin
            has_exception = 1;
            cause = `RISCV_CSR_MCAUSE_EXCODE_IAMA;
        end
  end
  else if (inst_type == OP_BLTU) begin
    if (m_gpr[rs1] < m_gpr[rs2]) begin
      rpc = cpc + sign_extend((imm[12:1] << 1), 13);
    end
        if (rpc % 2 != 0) begin
            has_exception = 1;
            cause = `RISCV_CSR_MCAUSE_EXCODE_IAMA;
        end
  end
  else if (inst_type == OP_BGEU) begin
    if (m_gpr[rs1] >= m_gpr[rs2]) begin
      rpc = cpc + sign_extend((imm[12:1] << 1), 13);
    end
        if (rpc % 2 != 0) begin
            has_exception = 1;
            cause = `RISCV_CSR_MCAUSE_EXCODE_IAMA;
        end
  end
  else if (inst_type == OP_LB) begin
    addr = m_gpr[rs1] + sign_extend(imm[11:0], 12);
        has_exception = check_lsu_exception(inst_type, addr);

        if (has_exception == 0) begin
            addr = va2pa(addr, 0);
        m_gpr[rd] = m_load(addr, 1, 1);
        end
  end
  else if (inst_type == OP_LH) begin
    addr = m_gpr[rs1] + sign_extend(imm[11:0], 12);
        has_exception = check_lsu_exception(inst_type, addr);

        if (has_exception == 0) begin
            addr = va2pa(addr, 0);
        m_gpr[rd] = m_load(addr, 2, 1);
        end
  end
  else if (inst_type == OP_LW) begin
    addr = m_gpr[rs1] + sign_extend(imm[11:0], 12);
        has_exception = check_lsu_exception(inst_type, addr);

        if (has_exception == 0) begin
            addr = va2pa(addr, 0);
        m_gpr[rd] = m_load(addr, 4, 1);
        end
  end
  else if (inst_type == OP_LD) begin
    addr = m_gpr[rs1] + sign_extend(imm[11:0], 12);
        has_exception = check_lsu_exception(inst_type, addr);

        if (has_exception == 0) begin
            addr = va2pa(addr, 0);
        m_gpr[rd] = m_load(addr, 8, 1);
        end
  end
  else if (inst_type == OP_LBU) begin
    addr = m_gpr[rs1] + sign_extend(imm[11:0], 12);
        has_exception = check_lsu_exception(inst_type, addr);

        if (has_exception == 0) begin
            addr = va2pa(addr, 0);
        m_gpr[rd] = m_load(addr, 1, 0);
        end
  end
  else if (inst_type == OP_LHU) begin
    addr = m_gpr[rs1] + sign_extend(imm[11:0], 12);
        has_exception = check_lsu_exception(inst_type, addr);

        if (has_exception == 0) begin
            addr = va2pa(addr, 0);
        m_gpr[rd] = m_load(addr, 2, 0);
        end
  end
  else if (inst_type == OP_LWU) begin
    addr = m_gpr[rs1] + sign_extend(imm[11:0], 12);
        has_exception = check_lsu_exception(inst_type, addr);

        if (has_exception == 0) begin
            addr = va2pa(addr, 0);
        m_gpr[rd] = m_load(addr, 4, 0);
        end
  end
  else if (inst_type == OP_FLW) begin
    addr = m_gpr[rs1] + sign_extend(imm[11:0], 12);
        has_exception = check_lsu_exception(inst_type, addr);

        if (has_exception == 0) begin
            addr = va2pa(addr, 0);
        end
  end
  else if (inst_type == OP_SB) begin
    addr = m_gpr[rs1] + sign_extend(imm[11:0], 12);
        has_exception = check_lsu_exception(inst_type, addr);

        if (has_exception == 0) begin
            addr = va2pa(addr, 0);
        m_store(addr, m_gpr[rs2], 1);
        end
  end
  else if (inst_type == OP_SH) begin
    addr = m_gpr[rs1] + sign_extend(imm[11:0], 12);
        has_exception = check_lsu_exception(inst_type, addr);

        if (has_exception == 0) begin
            addr = va2pa(addr, 0);
        m_store(addr, m_gpr[rs2], 2);
        end
  end
  else if (inst_type == OP_SW) begin
    addr = m_gpr[rs1] + sign_extend(imm[11:0], 12);
        has_exception = check_lsu_exception(inst_type, addr);

        if (has_exception == 0) begin
            addr = va2pa(addr, 0);
        m_store(addr, m_gpr[rs2], 4);
        end
  end
  else if (inst_type == OP_SD) begin
    addr = m_gpr[rs1] + sign_extend(imm[11:0], 12);
        has_exception = check_lsu_exception(inst_type, addr);

        if (has_exception == 0) begin
            addr = va2pa(addr, 0);
        m_store(addr, m_gpr[rs2], 8);
        end
  end
  else if (inst_type == OP_FSW) begin
    addr = m_gpr[rs1] + sign_extend(imm[11:0], 12);
        has_exception = check_lsu_exception(inst_type, addr);

        if (has_exception == 0) begin
            addr = va2pa(addr, 0);
        //m_store(addr, m_gpr[rs2], 4);
        end
  end
  else if (inst_type == OP_MUL) begin
    m_gpr[rd] = m_gpr[rs1] * m_gpr[rs2];
  end
  else if (inst_type == OP_MULH) begin
    tmp128_1 = signed'(m_gpr[rs1]);
    tmp128_2 = signed'(m_gpr[rs2]);
    tmp128_0 = tmp128_1 * tmp128_2;
    m_gpr[rd] = tmp128_0[127:64];
  end
  else if (inst_type == OP_MULHSU) begin
    tmp128_1 = signed'(m_gpr[rs1]);
    tmp128_2 = m_gpr[rs2];
    tmp128_0 = tmp128_1 * tmp128_2;
    m_gpr[rd] = tmp128_0[127:64];
  end
  else if (inst_type == OP_MULHU) begin
    tmp128_1 = m_gpr[rs1];
    tmp128_2 = m_gpr[rs2];
    tmp128_0 = tmp128_1 * tmp128_2;
    m_gpr[rd] = tmp128_0[127:64];
  end
  else if (inst_type == OP_MULW) begin
    tmp64 = m_gpr[rs1][31:0] * m_gpr[rs2][31:0];
    m_gpr[rd] = sign_extend(tmp64[31:0], 32);
  end
  else if (inst_type == OP_DIV) begin
    if (m_gpr[rs2] == 0) begin
      m_gpr[rd] = signed'(-1);
    end
    else if (m_gpr[rs1] == 64'h8000_0000_0000_0000 && signed'(m_gpr[rs2]) == -1) begin
      m_gpr[rd] = m_gpr[rs1];
    end
    else begin
      m_gpr[rd] = signed'(m_gpr[rs1]) / signed'(m_gpr[rs2]);
    end
  end
  else if (inst_type == OP_DIVU) begin
    if (m_gpr[rs2] == 0) begin
      m_gpr[rd] = 64'hffff_ffff_ffff_ffff;
    end
    else begin
      m_gpr[rd] = m_gpr[rs1] / m_gpr[rs2];
    end
  end
  else if (inst_type == OP_DIVUW) begin
    if (m_gpr[rs2][31:0] == 0) begin
      m_gpr[rd] = 64'hffff_ffff_ffff_ffff;
    end
    else begin
      tmp64 = m_gpr[rs1][31:0] / m_gpr[rs2][31:0];
      m_gpr[rd] = sign_extend(tmp64[31:0], 32);
    end
  end
  else if (inst_type == OP_DIVW) begin
    if (m_gpr[rs2][31:0] == 0) begin
      m_gpr[rd] = signed'(-1);
    end
    else begin
      tmp64 = signed'(m_gpr[rs1][31:0]) / signed'(m_gpr[rs2][31:0]);
      m_gpr[rd] = sign_extend(tmp64[31:0], 32);
    end
  end
  else if (inst_type == OP_REM) begin
    if (m_gpr[rs2] == 0) begin
      m_gpr[rd] = m_gpr[rs1];
    end
    else if (m_gpr[rs1] == 64'h8000_0000_0000_0000 && signed'(m_gpr[rs2]) == -1) begin
      m_gpr[rd] = 0;
    end
    else begin
      m_gpr[rd] = signed'(m_gpr[rs1]) % signed'(m_gpr[rs2]);
    end
  end
  else if (inst_type == OP_REMU) begin
    if (m_gpr[rs2] == 0) begin
      m_gpr[rd] = m_gpr[rs1];
    end
    else begin
      m_gpr[rd] = m_gpr[rs1] % m_gpr[rs2];
    end
  end
  else if (inst_type == OP_REMW) begin
    if (m_gpr[rs2][31:0] == 0) begin
      m_gpr[rd] = sign_extend(m_gpr[rs1][31:0], 32);
    end
    else begin
      tmp64 = signed'(m_gpr[rs1][31:0]) % signed'(m_gpr[rs2][31:0]);
      m_gpr[rd] = sign_extend(tmp64[31:0], 32);
    end
  end
  else if (inst_type == OP_REMUW) begin
    if (m_gpr[rs2][31:0] == 0) begin
      m_gpr[rd] = sign_extend(m_gpr[rs1][31:0], 32);
    end
    else begin
      tmp64 = m_gpr[rs1][31:0] % m_gpr[rs2][31:0];
      m_gpr[rd] = sign_extend(tmp64[31:0], 32);
    end
  end
  else if (inst_type == OP_FENCE) begin
    ;
  end
  else if (inst_type == OP_FENCEI) begin
    ;
  end
  else if (inst_type == OP_SFENCE) begin
    if (m_curr_priv_level == PRIV_LEVEL_UMODE) begin
            has_exception = 1;
            cause = `RISCV_CSR_MCAUSE_EXCODE_ILL;
        end
    else if (tvm == 1 && m_curr_priv_level == PRIV_LEVEL_SMODE) begin
            has_exception = 1;
            cause = `RISCV_CSR_MCAUSE_EXCODE_ILL;
        end
  end
  else if (inst_type == OP_WFI) begin
    if (m_curr_priv_level == PRIV_LEVEL_UMODE) begin
            has_exception = 1;
            cause = `RISCV_CSR_MCAUSE_EXCODE_ILL;
        end
    else if (tw == 1 && m_curr_priv_level == PRIV_LEVEL_SMODE) begin
            has_exception = 1;
            cause = `RISCV_CSR_MCAUSE_EXCODE_ILL;
        end
  end
    else if (inst_type == OP_CSRRW) begin
        has_exception = cal_csr(inst_type, imm[16:5], rs1, rd);
        if (has_exception == 1) begin
            cause = `RISCV_CSR_MCAUSE_EXCODE_ILL;
        end
    end
    else if (inst_type == OP_CSRRS) begin
        has_exception = cal_csr(inst_type, imm[16:5], rs1, rd);
        if (has_exception == 1) begin
            cause = `RISCV_CSR_MCAUSE_EXCODE_ILL;
        end
    end
    else if (inst_type == OP_CSRRC) begin
        has_exception = cal_csr(inst_type, imm[16:5], rs1, rd);
        if (has_exception == 1) begin
            cause = `RISCV_CSR_MCAUSE_EXCODE_ILL;
        end
    end
    else if (inst_type == OP_CSRRWI) begin
        has_exception = cal_csr(inst_type, imm[16:5], imm[4:0], rd);
        if (has_exception == 1) begin
            cause = `RISCV_CSR_MCAUSE_EXCODE_ILL;
        end
    end
    else if (inst_type == OP_CSRRSI) begin
        has_exception = cal_csr(inst_type, imm[16:5], imm[4:0], rd);
        if (has_exception == 1) begin
            cause = `RISCV_CSR_MCAUSE_EXCODE_ILL;
        end
    end
    else if (inst_type == OP_CSRRCI) begin
        has_exception = cal_csr(inst_type, imm[16:5], imm[4:0], rd);
        if (has_exception == 1) begin
            cause = `RISCV_CSR_MCAUSE_EXCODE_ILL;
        end
    end
    else if (inst_type == OP_ECALL) begin
        has_exception = 1;
    if (m_curr_priv_level == PRIV_LEVEL_UMODE) begin
            cause = `RISCV_CSR_MCAUSE_EXCODE_UCALL;
        end
        else if (m_curr_priv_level == PRIV_LEVEL_SMODE) begin
            cause = `RISCV_CSR_MCAUSE_EXCODE_SCALL;
        end
        else if (m_curr_priv_level == PRIV_LEVEL_MMODE) begin
            cause = `RISCV_CSR_MCAUSE_EXCODE_MCALL;
        end
    end
    else if (inst_type == OP_EBREAK) begin
        has_exception = 1;
        cause = `RISCV_CSR_MCAUSE_EXCODE_BKPT;
    end
    else if (inst_type == OP_MRET) begin
    if (m_curr_priv_level == PRIV_LEVEL_UMODE) begin
            has_exception = 1;
            cause = `RISCV_CSR_MCAUSE_EXCODE_ILL;
        end
    else if (m_curr_priv_level == PRIV_LEVEL_SMODE) begin
            has_exception = 1;
            cause = `RISCV_CSR_MCAUSE_EXCODE_ILL;
        end
        else begin
            rpc = mepc;

            // update mstatus related bits and priv level when returning from trap
            mie = mpie;
            mpie = 1;
            m_curr_priv_level = privilege_level_e'(mpp); // TODO: review with Neo Fang
            mpp = 0;
        end
    end
    else if (inst_type == OP_SRET) begin
    if (m_curr_priv_level == PRIV_LEVEL_UMODE) begin
            has_exception = 1;
            cause = `RISCV_CSR_MCAUSE_EXCODE_ILL;
        end
    else if (tsr == 1 && m_curr_priv_level == PRIV_LEVEL_SMODE) begin
            has_exception = 1;
            cause = `RISCV_CSR_MCAUSE_EXCODE_ILL;
        end
        else begin
            rpc = sepc;

            // update mstatus related bits and priv level when returning from trap
            sie = spie;
            spie = 1;
            m_curr_priv_level = privilege_level_e'(spp); // TODO: review with Neo Fang
            spp = 0;
        end
    end
    else if (inst_type == OP_C_LWSP) begin
        if (rd == 0) begin
            has_exception = 1;
            cause = `RISCV_CSR_MCAUSE_EXCODE_ILL;
        end
        else begin
        addr = m_gpr[2] + {imm[7:2], 2'b0};
            has_exception = check_lsu_exception(inst_type, addr);

            if (has_exception == 0) begin
                addr = va2pa(addr, 0);
            m_gpr[rd] = m_load(addr, 4, 1);
            end
        end
  end
    else if (inst_type == OP_C_LDSP) begin
        if (rd == 0) begin
            has_exception = 1;
            cause = `RISCV_CSR_MCAUSE_EXCODE_ILL;
        end
        else begin
        addr = m_gpr[2] + {imm[8:3], 3'b0};
            has_exception = check_lsu_exception(inst_type, addr);

            if (has_exception == 0) begin
                addr = va2pa(addr, 0);
            m_gpr[rd] = m_load(addr, 8, 1);
            end
        end
  end
    else if (inst_type == OP_C_SWSP) begin
    addr = m_gpr[2] + {imm[7:2], 2'b0};
        has_exception = check_lsu_exception(inst_type, addr);

        if (has_exception == 0) begin
            addr = va2pa(addr, 0);
        m_store(addr, m_gpr[rs2], 4);
        end
  end
    else if (inst_type == OP_C_SDSP) begin
    addr = m_gpr[2] + {imm[8:3], 3'b0};
        has_exception = check_lsu_exception(inst_type, addr);

        if (has_exception == 0) begin
            addr = va2pa(addr, 0);
        m_store(addr, m_gpr[rs2], 8);
        end
  end
    else if (inst_type == OP_C_LW) begin
    addr = m_gpr[rs1] + {imm[6:2], 2'b0};
        has_exception = check_lsu_exception(inst_type, addr);

        if (has_exception == 0) begin
            addr = va2pa(addr, 0);
        m_gpr[rd] = m_load(addr, 4, 1);
        end
  end
    else if (inst_type == OP_C_LD) begin
    addr = m_gpr[rs1] + {imm[7:3], 3'b0};
        has_exception = check_lsu_exception(inst_type, addr);

        if (has_exception == 0) begin
            addr = va2pa(addr, 0);
        m_gpr[rd] = m_load(addr, 8, 1);
        end
  end
    else if (inst_type == OP_C_SW) begin
    addr = m_gpr[rs1] + {imm[6:2], 2'b0};
        has_exception = check_lsu_exception(inst_type, addr);

        if (has_exception == 0) begin
            addr = va2pa(addr, 0);
        m_store(addr, m_gpr[rs2], 4);
        end
  end
    else if (inst_type == OP_C_SD) begin
    addr = m_gpr[rs1] + {imm[7:3], 3'b0};
        has_exception = check_lsu_exception(inst_type, addr);

        if (has_exception == 0) begin
            addr = va2pa(addr, 0);
        m_store(addr, m_gpr[rs2], 8);
        end
  end
    else if (inst_type == OP_C_J) begin
    rpc = cpc + sign_extend((imm[11:1] << 1), 12);
  end
    else if (inst_type == OP_C_JR) begin
        if (rs1 == 0) begin
            has_exception = 1;
            cause = `RISCV_CSR_MCAUSE_EXCODE_ILL;
        end
        else begin
        rpc = m_gpr[rs1] & 'hffff_ffff_ffff_fffe;
        end
  end
    else if (inst_type == OP_C_JALR) begin
        if (rs1 == 0) begin
            has_exception = 1;
            cause = `RISCV_CSR_MCAUSE_EXCODE_ILL;
        end
        else begin
        rpc = m_gpr[rs1] & 'hffff_ffff_ffff_fffe;
        m_gpr[1] = cpc + 2;
        end
  end
    else if (inst_type == OP_C_BEQZ) begin
    if (m_gpr[rs1] == 0) begin
      rpc = cpc + sign_extend((imm[8:1] << 1), 9);
    end
  end
    else if (inst_type == OP_C_BNEZ) begin
    if (m_gpr[rs1] != 0) begin
      rpc = cpc + sign_extend((imm[8:1] << 1), 9);
    end
  end
    else if (inst_type == OP_C_LI) begin
        m_gpr[rd] = sign_extend(imm[5:0], 6);
  end
    else if (inst_type == OP_C_LUI) begin
        if (imm[17:12] == 0 || rd == 2) begin
            has_exception = 1;
            cause = `RISCV_CSR_MCAUSE_EXCODE_ILL;
        end
        else begin
            m_gpr[rd] = sign_extend({imm[17:12], 12'b0}, 18);
        end
  end
    else if (inst_type == OP_C_ADDI) begin
        if (rd == 0) begin
            has_exception = 1;
            cause = `RISCV_CSR_MCAUSE_EXCODE_ILL;
        end
        else begin
        m_gpr[rd] = m_gpr[rs1] + sign_extend(imm[5:0], 6);
        end
  end
    else if (inst_type == OP_C_ADDIW) begin
        if (rd == 0) begin
            has_exception = 1;
            cause = `RISCV_CSR_MCAUSE_EXCODE_ILL;
        end
        else begin
        simm64 = sign_extend(imm[5:0], 6);
        tmp64 = m_gpr[rs1][31:0] + simm64[31:0];
        m_gpr[rd] = sign_extend(tmp64[31:0], 32);
        end
  end
    else if (inst_type == OP_C_ADDI16SP) begin
        if (imm[9:4] == 0) begin
            has_exception = 1;
            cause = `RISCV_CSR_MCAUSE_EXCODE_ILL;
        end
        else begin
            m_gpr[2] = m_gpr[2] + sign_extend({imm[9:4], 4'b0}, 10);
        end
  end
    else if (inst_type == OP_C_ADDI4SPN) begin
        if (imm[9:2] == 0) begin
            has_exception = 1;
            cause = `RISCV_CSR_MCAUSE_EXCODE_ILL;
        end
        else begin
        m_gpr[rd] = m_gpr[2] + {imm[9:2], 2'b0};
        end
  end
    else if (inst_type == OP_C_SLLI) begin
        if (imm[5:0] == 0) begin
            has_exception = 1;
            cause = `RISCV_CSR_MCAUSE_EXCODE_ILL;
        end
        else begin
        m_gpr[rd] = m_gpr[rs1] << imm[5:0];
        end
  end
    else if (inst_type == OP_C_SRLI) begin
        if (imm[5:0] == 0) begin
            has_exception = 1;
            cause = `RISCV_CSR_MCAUSE_EXCODE_ILL;
        end
        else begin
        m_gpr[rd] = m_gpr[rs1] >> imm[5:0];
        end
  end
    else if (inst_type == OP_C_SRAI) begin
        if (imm[5:0] == 0) begin
            has_exception = 1;
            cause = `RISCV_CSR_MCAUSE_EXCODE_ILL;
        end
        else begin
        m_gpr[rd] = sign_extend((m_gpr[rs1] >> imm[5:0]), (64 - imm[5:0]));
        end
  end
    else if (inst_type == OP_C_ANDI) begin
    m_gpr[rd] = m_gpr[rs1] & sign_extend(imm[5:0], 6);
  end
    else if (inst_type == OP_C_MV) begin
        if (rs2 == 0) begin
            has_exception = 1;
            cause = `RISCV_CSR_MCAUSE_EXCODE_ILL;
        end
        else begin
        m_gpr[rd] = m_gpr[rs2];
        end
  end
    else if (inst_type == OP_C_ADD) begin
        if (rs2 == 0) begin
            has_exception = 1;
            cause = `RISCV_CSR_MCAUSE_EXCODE_ILL;
        end
        else begin
        m_gpr[rd] = m_gpr[rs1] + m_gpr[rs2];
        end
  end
    else if (inst_type == OP_C_AND) begin
    m_gpr[rd] = m_gpr[rs1] & m_gpr[rs2];
  end
    else if (inst_type == OP_C_OR) begin
    m_gpr[rd] = m_gpr[rs1] | m_gpr[rs2];
  end
    else if (inst_type == OP_C_XOR) begin
    m_gpr[rd] = m_gpr[rs1] ^ m_gpr[rs2];
  end
    else if (inst_type == OP_C_SUB) begin
    m_gpr[rd] = m_gpr[rs1] - m_gpr[rs2];
  end
    else if (inst_type == OP_C_ADDW) begin
    tmp64 = m_gpr[rs1][31:0] + m_gpr[rs2][31:0];
    m_gpr[rd] = sign_extend(tmp64[31:0], 32);
  end
    else if (inst_type == OP_C_SUBW) begin
    tmp64 = m_gpr[rs1][31:0] - m_gpr[rs2][31:0];
    m_gpr[rd] = sign_extend(tmp64[31:0], 32);
  end
    else if (inst_type == OP_C_NOP) begin
  end
    else if (inst_type == OP_C_EBREAK) begin
        has_exception = 1;
        cause = `RISCV_CSR_MCAUSE_EXCODE_BKPT;
  end
    else if (inst_type > 'h69 && inst_type < 'h8e) begin
  end
  else begin
    `uvm_info("debug", $psprintf("not support this instruction yet for caculate_op(), inst_type = 0x%0x, pc = 0x%0x\n", inst_type, cpc), UVM_HIGH);
        has_exception = 1;
        cause = `RISCV_CSR_MCAUSE_EXCODE_ILL;
  end

  if (ctype == RETURN_GPR) begin
        if (has_exception == 0) begin
        rpc = m_gpr[rd];
        end
        else begin
            rpc = 'hdeadbeef_deadbeef;
        end
  end
    else if (has_exception == 1) begin
        if (medeleg[cause] == 0 ||
            m_curr_priv_level == PRIV_LEVEL_MMODE ||
            cause == `RISCV_CSR_MCAUSE_EXCODE_SCALL ||
            cause == `RISCV_CSR_MCAUSE_EXCODE_MCALL) begin
            // trap to M-mode
            mepc = cpc;
            rpc = m_curr_mmode_trap_vector;

            // update mstatus related bits when entering trap
            mpie = mie;
            mie = 0;
            mpp = m_curr_priv_level;

            // switch to M-mode when entering trap
            m_curr_priv_level = PRIV_LEVEL_MMODE;

            // update cause
            mcause = cause;
        end
        else begin
            // trap delegated to S-mode
            sepc = cpc;
            rpc = m_curr_smode_trap_vector;

            // update mstatus/sstatus related bits when entering trap
            spie = sie;
            sie = 0;
            spp = m_curr_priv_level;

            // switch to S-mode when entering trap
            m_curr_priv_level = PRIV_LEVEL_SMODE;

            // update cause
            scause = cause;
        end
    end
    else begin
        minstret++;
    end

  // for x0, its value is always 0 and can't be overriden
  if (rd == 0) begin
    m_gpr[rd] = 0;
  end

  return rpc;
endfunction

function void riscv_base_seq::gen_inst_result();
  bit [63:0] curr_pc;
  bit [63:0] next_pc;
  //riscv_inst_result_txn txn;
  int same_pc_times = 0;
    bit [31:0] inst_code;
    bit [63:0] pc_pa;

  curr_pc = init_start_pc;

  for (int i=0; i<32; i++) begin
    m_gpr[i] = 0;
  end
  init_m_mem();
  init_csr();

  while (1) begin
    if (same_pc_times < max_same_pc_times) begin
      if (inst_arr.exists(curr_pc)) begin
                //print_gpr(); //for debug
                inst_code = 0;
                for (int i=0; i<inst_arr[curr_pc].inst_bin_code_size; i++) begin
                    pc_pa = get_pa(inst_arr[curr_pc].pc+i, 1, 0);
                    inst_code += m_mem[pc_pa] << 8*i;
                end
                inst_arr[curr_pc].inst_decode(inst_code);

                next_pc = calculate_op(inst_arr[curr_pc].inst_type, curr_pc, inst_arr[curr_pc].rd, inst_arr[curr_pc].rs1, inst_arr[curr_pc].rs2, inst_arr[curr_pc].imm);

                `uvm_info("cal_op", $psprintf("curr_pc = 0x%0x, inst_type = 0x%0x, rd = %0d, rs1 = %0d, rs2 = %0d, imm = 0x%0x, next_pc = 0x%0x, m_gpr[rs1] = 0x%0x, m_gpr[rs2] = 0x%0x, m_gpr[rd] = 0x%0x, is_change_store_inst = %0d, inst_code = 0x%0x, cause = %0d, instret = %0d", curr_pc, inst_arr[curr_pc].inst_type, inst_arr[curr_pc].rd, inst_arr[curr_pc].rs1, inst_arr[curr_pc].rs2, inst_arr[curr_pc].imm, next_pc, m_gpr[inst_arr[curr_pc].rs1], m_gpr[inst_arr[curr_pc].rs2], m_gpr[inst_arr[curr_pc].rd], inst_arr[curr_pc].is_change_store_inst, inst_code, cause, minstret), UVM_DEBUG);
                //print_gpr(); //for debug

                if (inst_arr[curr_pc].is_rd_valid && rsvd_gpr_arr.exists(inst_arr[curr_pc].rd) && !m_boot_pc.exists(curr_pc) && !m_tvec_pc.exists(curr_pc) && next_pc != m_curr_mmode_trap_vector && next_pc != m_curr_smode_trap_vector && inst_arr[curr_pc].is_key_inst == 0 && (inst_arr[curr_pc].inst_type inside {OP_FEQ_S, OP_FLT_S, OP_FLE_S, OP_FCLASS_S, OP_FMV_X_S, OP_FCVT_W_S, OP_FCVT_WU_S, OP_FCVT_L_S, OP_FCVT_LU_S} || !(inst_arr[curr_pc].inst_type inside {['h70:'h8d]})) ) begin
                    `uvm_fatal("fatal", $psprintf("rd should not be in rsvd_arr, curr_pc = 0x%0x, inst_type = 0x%0x, rd = %0d, rs1 = %0d, rs2 = %0d, imm = 0x%0x", curr_pc, inst_arr[curr_pc].inst_type, inst_arr[curr_pc].rd, inst_arr[curr_pc].rs1, inst_arr[curr_pc].rs2, inst_arr[curr_pc].imm));
                end
        
                // TODO: confirm with Neo Fang that riscv_inst)result_txn is not needed.
                //txn = riscv_inst_result_txn::type_id::create("txn");
                //txn.pc = next_pc;
                //for (int i=0; i<32; i++) begin
                //  txn.gpr[i] = m_gpr[i];
                //end
                //tb_exp_queue.push_back(txn);

                if (next_pc == curr_pc) begin
                  same_pc_times++;
                end
                else begin
                  same_pc_times = 0;
                end

                curr_pc = next_pc;
      end
      else begin
        `uvm_fatal("base_seq", $psprintf("pc 0x%0x is not existed in inst_arr\n", curr_pc));
      end
    end
    else begin
      break;
    end
  end
endfunction

// generate the instruction result which is stored in inst_arr[]
// if specified last_pc(default all Fs), then exit for last pc
function void riscv_base_seq::gen_curr_inst_result(bit[63:0] last_pc);
  bit [63:0] curr_pc;
  bit [63:0] next_pc;
  int same_pc_times = 0;
    bit [31:0] inst_code;
    bit [63:0] pc_pa;

  if (inst_arr.num() == 0) begin
    `uvm_warning("warning", "In gen_curr_inst_result(), inst_arr is empty\n");
    return;
  end

  curr_pc = init_start_pc;

  for (int i=0; i<32; i++) begin
    m_gpr[i] = 0;
  end
  init_m_mem();
  init_csr();

  while (1) begin
    if (same_pc_times < max_same_pc_times) begin
      if (inst_arr.exists(curr_pc)) begin
                inst_code = 0;
                for (int i=0; i<inst_arr[curr_pc].inst_bin_code_size; i++) begin
          pc_pa = get_pa(inst_arr[curr_pc].pc+i, 1, 0);
                    inst_code += m_mem[pc_pa] << 8*i;
                end
                inst_arr[curr_pc].inst_decode(inst_code);

        next_pc = calculate_op(inst_arr[curr_pc].inst_type, curr_pc, inst_arr[curr_pc].rd, inst_arr[curr_pc].rs1, inst_arr[curr_pc].rs2, inst_arr[curr_pc].imm);

        `uvm_info("debug", $psprintf("in gen_curr_inst_result(), curr_pc = 0x%0x, next_pc = 0x%0x, inst_type = 0x%0x, rd = %0d, rs1 = %0d, rs2 = %0d, imm = 0x%0x, cause = 0x%0x", curr_pc, next_pc, inst_arr[curr_pc].inst_type, inst_arr[curr_pc].rd, inst_arr[curr_pc].rs1, inst_arr[curr_pc].rs2, inst_arr[curr_pc].imm, cause), UVM_DEBUG);
        //print_gpr();

                if (next_pc == last_pc) begin
          `uvm_info("debug", $psprintf("exit for last pc 0x%0x", next_pc), UVM_HIGH);
          break;
        end

        if (next_pc == curr_pc) begin
          same_pc_times++;
        end
        else begin
          same_pc_times = 0;
        end

        curr_pc = next_pc;
      end
      else begin
                break;
      end
    end
    else begin
      break;
    end
  end
endfunction

function bit riscv_base_seq::gen_lsu_addr(bit[63:0] min_addr, bit[63:0] max_addr, ref riscv_inst_base_txn tr);
  bit [63:0] base;
  bit [4:0] m_rs1;
  bit [63:0] pa;
    bit found_valid_base = 0;
    int loop_cnt = 0;

    // these C-extension LSU instructions use fixed rs1, can't be changed
    if (tr.inst_type == OP_C_LWSP || tr.inst_type == OP_C_LDSP || tr.inst_type == OP_C_SWSP || tr.inst_type == OP_C_SDSP) begin
        tr.rs1 = 2;
    end
    else begin
      m_rs1 = tr.rs1;
        found_valid_base = ~get_legal_lsu_param(tr.inst_type, m_rs1, min_addr, max_addr);
      tr.rs1 = m_rs1;
    end

  base = m_gpr[tr.rs1];
  if (tr.inst_type == OP_LB || tr.inst_type == OP_LBU || tr.inst_type == OP_SB) begin
        do begin
            if (loop_cnt == 50) begin
          `uvm_info("debug", $psprintf("After looping 50 times, generated target_addr is still illegal, change it to load inst, pc = 0x%0x, inst_type = 0x%0x", tr.pc, tr.inst_type), UVM_HIGH);
                tr.inst_type = (($urandom%2)==0) ? OP_LB : OP_LBU;
        end

        void'(tr.randomize(imm_64) with {
          imm_64 dist {0:/1, [1:5]:/3, [6:'h7ff]:/15, ['hffff_ffff_ffff_f800:'hffff_ffff_ffff_fff9]:/15, ['hffff_ffff_ffff_fffa:'hffff_ffff_ffff_fffe]:/3, 'hffff_ffff_ffff_ffff:/1};
                if (found_valid_base == 1) {
              base + signed'(imm_64) >= min_addr;
              base + signed'(imm_64) <= max_addr;
                }
        });
            
            tr.imm = tr.imm_64[31:0];
          tr.target = base + signed'(tr.imm_64);
            loop_cnt++;
        end while (check_lsu_target_addr(tr.inst_type, tr.target, 1) == 1);
  end
  else if (tr.inst_type == OP_LH || tr.inst_type == OP_LHU || tr.inst_type == OP_SH) begin
        do begin
            if (loop_cnt == 50) begin
          `uvm_info("debug", $psprintf("After looping 50 times, generated target_addr is still illegal, change it to load inst, pc = 0x%0x, inst_type = 0x%0x", tr.pc, tr.inst_type), UVM_HIGH);
                tr.inst_type = (($urandom%2)==0) ? OP_LH : OP_LHU;
        end

        void'(tr.randomize(imm_64) with {
          imm_64 dist {0:/1, [1:5]:/3, [6:'h7ff]:/15, ['hffff_ffff_ffff_f800:'hffff_ffff_ffff_fff9]:/15, ['hffff_ffff_ffff_fffa:'hffff_ffff_ffff_fffe]:/3, 'hffff_ffff_ffff_ffff:/1};
                if (found_valid_base == 1) {
              base + signed'(imm_64) >= min_addr;
              base + signed'(imm_64) <= max_addr;
                }
                if (is_lsu_mis_align == 0) {
              (base + signed'(imm_64)) % 2 == 0;
                }
                else {
              ((base + signed'(imm_64)) % 2 == 0) dist {0:/1, 1:/10};
                }
        });
            
            tr.imm = tr.imm_64[31:0];
          tr.target = base + signed'(tr.imm_64);
            loop_cnt++;
        end while (check_lsu_target_addr(tr.inst_type, tr.target, 2) == 1);
  end
  else if (tr.inst_type == OP_LW || tr.inst_type == OP_LWU || tr.inst_type == OP_SW || tr.inst_type == OP_FLW || tr.inst_type == OP_FSW) begin
        do begin
            if (loop_cnt == 50) begin
          `uvm_info("debug", $psprintf("After looping 50 times, generated target_addr is still illegal, change it to load inst, pc = 0x%0x, inst_type = 0x%0x", tr.pc, tr.inst_type), UVM_HIGH);
                if (tr.inst_type == OP_SW) begin
                    tr.inst_type = (($urandom%2)==0) ? OP_LW : OP_LWU;
                end
                else if (tr.inst_type == OP_FSW) begin
                    tr.inst_type = OP_FLW;
                end
                else begin
                    `uvm_fatal("fatal", "impossible case");
                end
        end

        void'(tr.randomize(imm_64) with {
          imm_64 dist {0:/1, [1:5]:/3, [6:'h7ff]:/15, ['hffff_ffff_ffff_f800:'hffff_ffff_ffff_fff9]:/15, ['hffff_ffff_ffff_fffa:'hffff_ffff_ffff_fffe]:/3, 'hffff_ffff_ffff_ffff:/1};
                if (found_valid_base == 1) {
              base + signed'(imm_64) >= min_addr;
              base + signed'(imm_64) <= max_addr;
                }
                if (is_lsu_mis_align == 0) {
              (base + signed'(imm_64)) % 4 == 0;
                }
                else {
              ((base + signed'(imm_64)) % 4 == 0) dist {0:/1, 1:/10};
                }
        });
            
            tr.imm = tr.imm_64[31:0];
          tr.target = base + signed'(tr.imm_64);
            loop_cnt++;
        end while (check_lsu_target_addr(tr.inst_type, tr.target, 4) == 1);
  end
  else if (tr.inst_type == OP_LD || tr.inst_type == OP_SD) begin
        do begin
            if (loop_cnt == 50) begin
          `uvm_info("debug", $psprintf("After looping 50 times, generated target_addr is still illegal, change it to load inst, pc = 0x%0x, inst_type = 0x%0x", tr.pc, tr.inst_type), UVM_HIGH);
                tr.inst_type = OP_LD;
        end

        void'(tr.randomize(imm_64) with {
          imm_64 dist {0:/1, [1:5]:/3, [6:'h7ff]:/15, ['hffff_ffff_ffff_f800:'hffff_ffff_ffff_fff9]:/15, ['hffff_ffff_ffff_fffa:'hffff_ffff_ffff_fffe]:/3, 'hffff_ffff_ffff_ffff:/1};
                if (found_valid_base == 1) {
              base + signed'(imm_64) >= min_addr;
              base + signed'(imm_64) <= max_addr;
                }
                if (is_lsu_mis_align == 0) {
              (base + signed'(imm_64)) % 8 == 0;
                }
                else {
              ((base + signed'(imm_64)) % 8 == 0) dist {0:/1, 1:/10};
                }
        });
           
            tr.imm = tr.imm_64[31:0];
          tr.target = base + signed'(tr.imm_64);
            loop_cnt++;
        end while (check_lsu_target_addr(tr.inst_type, tr.target, 8) == 1);
  end
    else if (tr.inst_type == OP_C_LWSP || tr.inst_type == OP_C_SWSP || tr.inst_type == OP_C_LW || tr.inst_type == OP_C_SW) begin
        do begin
            if (loop_cnt == 10) begin
          `uvm_info("debug", $psprintf("After looping 10 times, generated target_addr is still illegal, change it to load inst, pc = 0x%0x, inst_type = 0x%0x", tr.pc, tr.inst_type), UVM_HIGH);
                if (tr.inst_type == OP_C_SWSP) begin
                    tr.inst_type = OP_C_LWSP;
                end
                else if (tr.inst_type == OP_C_SW) begin
                    tr.inst_type = OP_C_LW;
                end
                else begin
                    `uvm_fatal("fatal", "impossible case");
                end
        end

        void'(tr.randomize(imm) with {
                imm[1:0] == 0;
                if (tr.inst_type == OP_C_LWSP || tr.inst_type == OP_C_SWSP) {
              imm[7:2] dist {0:=1, [1:'h3e]:=1, 'h3f:=1};
                    imm[31:8] == 0;
                }
                else {
              imm[6:2] dist {0:=1, [1:'h1e]:=1, 'h1f:=1};
                    imm[31:7] == 0;
                }

                if (found_valid_base == 1) {
              base + imm >= min_addr;
              base + imm <= max_addr;
                }
        });
            
            tr.target = base + tr.imm;
            loop_cnt++;
        end while (check_lsu_target_addr(tr.inst_type, tr.target, 4) == 1);
  end
    else if (tr.inst_type == OP_C_LDSP || tr.inst_type == OP_C_SDSP || tr.inst_type == OP_C_LD || tr.inst_type == OP_C_SD) begin
        do begin
            if (loop_cnt == 10) begin
          `uvm_info("debug", $psprintf("After looping 10 times, generated target_addr is still illegal, change it to load inst, pc = 0x%0x, inst_type = 0x%0x", tr.pc, tr.inst_type), UVM_HIGH);
                if (tr.inst_type == OP_C_SDSP) begin
                    tr.inst_type = OP_C_LDSP;
                end
                else if (tr.inst_type == OP_C_SD) begin
                    tr.inst_type = OP_C_LD;
                end
                else begin
                    `uvm_fatal("fatal", "impossible case");
                end
        end

        void'(tr.randomize(imm) with {
                imm[2:0] == 0;
                if (tr.inst_type == OP_C_LDSP || tr.inst_type == OP_C_SDSP) {
              imm[8:3] dist {0:=1, [1:'h3e]:=1, 'h3f:=1};
                    imm[31:9] == 0;
                }
                else {
              imm[7:3] dist {0:=1, [1:'h1e]:=1, 'h1f:=1};
                    imm[31:8] == 0;
                }

                if (found_valid_base == 1) {
              base + imm >= min_addr;
              base + imm <= max_addr;
                }
        });
            
            tr.target = base + tr.imm;
            loop_cnt++;
        end while (check_lsu_target_addr(tr.inst_type, tr.target, 8) == 1);
  end
    else begin
        `uvm_fatal("debug", $psprintf("Unexpected inst_type 0x%0x, should only be LSU inst", tr.inst_type));
    end

    if (check_mem_trans_access_violation(tr.target, get_lsu_size(tr.inst_type), 0, is_load_inst(tr.inst_type)) == 0) begin
      pa = va2pa(tr.target, 0);
      insert_lsu_bus_fault(tr.inst_type, pa);
    end
  return 0;
endfunction

function bit[63:0] riscv_base_seq::get_lsu_va(riscv_inst_base_txn tr);
  bit [63:0] lsu_va;

  if (tr.inst_type == OP_C_LWSP || tr.inst_type == OP_C_SWSP) begin
        lsu_va = m_gpr[2] + {tr.imm[7:2], 2'b0};
    end
  else if (tr.inst_type == OP_C_LDSP || tr.inst_type == OP_C_SDSP) begin
        lsu_va = m_gpr[2] + {tr.imm[8:3], 3'b0};
    end
  else if (tr.inst_type == OP_C_LW || tr.inst_type == OP_C_SW) begin
        lsu_va = m_gpr[tr.rs1] + {tr.imm[6:2], 2'b0};
    end
  else if (tr.inst_type == OP_C_LD || tr.inst_type == OP_C_SD) begin
        lsu_va = m_gpr[tr.rs1] + {tr.imm[7:3], 3'b0};
    end
    else begin
        lsu_va = m_gpr[tr.rs1] + sign_extend(tr.imm[11:0], 12);
    end

  return lsu_va;
endfunction

function bit[63:0] riscv_base_seq::get_lsu_pa(riscv_inst_base_txn tr);
  bit [63:0] lsu_va;
  bit [63:0] lsu_pa;

    lsu_va = get_lsu_va(tr);
    lsu_pa = va2pa(lsu_va, 0);

  return lsu_pa;
endfunction

// get LSU access size
function int riscv_base_seq::get_lsu_size(inst_type_e inst_type);
  if (inst_type == OP_LB || inst_type == OP_LBU || inst_type == OP_SB) begin
        return 1;
    end
    else if (inst_type == OP_LH || inst_type == OP_LHU || inst_type == OP_SH) begin
        return 2;
    end
    else if (inst_type == OP_LW || inst_type == OP_LWU || inst_type == OP_SW || inst_type == OP_FLW || inst_type == OP_FSW || inst_type == OP_C_LWSP || inst_type == OP_C_LW || inst_type == OP_C_SWSP || inst_type == OP_C_SW) begin
        return 4;
    end
    else if (inst_type == OP_LD || inst_type == OP_SD || inst_type == OP_C_LDSP || inst_type == OP_C_LD || inst_type == OP_C_SDSP || inst_type == OP_C_SD) begin
        return 8;
    end
    else begin
        `uvm_fatal("fatal", $psprintf("unexpected inst_type 0x%0x for get_lsu_size(), should only be LSU inst_type", inst_type));
    end
endfunction

// get fetch byte size
function int riscv_base_seq::get_fetch_size(inst_type_e inst_type);
  if (inst_type > OP_ILLEGAL) begin  // c-extension instruction
      return 2;
    end
    else begin
      return 4;
    end
endfunction

// check if there is exception for LSU instruction
function bit riscv_base_seq::check_lsu_exception(inst_type_e inst_type, bit[63:0] va);
    bit has_exception = 0;
    int align_bytes;
    bit [63:0] pa;
    int expt_type = 0; // 0:access fault, 1:address mis-align, 2:page fault

  align_bytes = get_lsu_size(inst_type);

    if (va % align_bytes != 0) begin
        has_exception = 1;
        expt_type = 1;
    end
    else if (check_mem_trans_access_violation(va, get_lsu_size(inst_type), 0, is_load_inst(inst_type)) == 1) begin
        has_exception = 1;
        if (check_page_fault_violation(va, get_lsu_size(inst_type), 0, is_load_inst(inst_type)) == 1) begin
            expt_type = 2;
        end
    end
    else begin
        pa = va2pa(va, 0);

        // check if there is any voilation for pa
    // NEED_CHANGE
    end

    // update cause
    if (has_exception == 1) begin
        if (expt_type == 0) begin // access fault
            if (is_load_inst(inst_type) == 1) begin
                cause = `RISCV_CSR_MCAUSE_EXCODE_LACC_FAULT;
            end
            else begin
                cause = `RISCV_CSR_MCAUSE_EXCODE_SACC_FAULT;
            end
        end
        else if (expt_type == 1) begin // address mis-align
            if (is_load_inst(inst_type) == 1) begin
                cause = `RISCV_CSR_MCAUSE_EXCODE_LAMA;
            end
            else begin
                cause = `RISCV_CSR_MCAUSE_EXCODE_SAMA;
            end
        end
        else begin  // page fault
            if (is_load_inst(inst_type) == 1) begin
                cause = `RISCV_CSR_MCAUSE_EXCODE_LPAGE_FAULT;
            end
            else begin
                cause = `RISCV_CSR_MCAUSE_EXCODE_SPAGE_FAULT;
            end
        end
    end

    return has_exception;
endfunction

// Insert memory bus fault
// NEED_CHANGE
function void riscv_base_seq::insert_lsu_bus_fault(inst_type_e inst_type, bit[63:0] addr);
    bit [63:0] tcm_tlb_miss_addr;
  bit [63:0] fbif_fault_addr;

    //if (get_pa_range(addr) == PA_RANGE_IMEM) begin
    //    tcm_tlb_miss_addr = addr & 'hffff_ffff_ffff_ff00;
  //  if (!riscv_mem::tcm_tlb_err.exists(tcm_tlb_miss_addr)) begin
  //    if ((is_itcm_error == 1) && (!m_init_mem.exists(addr)) && (is_overlap_with_rsvd_code(addr, 'hffff_ffff_ffff_ff00) == 0) && ($urandom() % itcm_bus_err_freq == 0)) begin
    //        riscv_mem::tcm_tlb_err[tcm_tlb_miss_addr] = 1;
    //        `uvm_info("debug", $psprintf("inserting itcm fault for addr 0x%0x", tcm_tlb_miss_addr), UVM_HIGH);
  //    end
  //  end
    //end
    //if (get_pa_range(addr) == PA_RANGE_EXTMEM1 || get_pa_range(addr) == PA_RANGE_EXTMEM2 || get_pa_range(addr) == PA_RANGE_EXTMEM3 || get_pa_range(addr) == PA_RANGE_EXTMEM4) begin
  //  fbif_fault_addr = addr & 'hffff_ffff_ffff_ffc0;
  //  if (is_load_inst(inst_type) == 1) begin
  //    if (!riscv_mem::fbif_err.exists(fbif_fault_addr) && $urandom % fbif_bus_err_freq == 0) begin
  //      if ((is_fbif_error == 1) && (!m_init_mem.exists(addr)) && (is_overlap_with_rsvd_code(addr, 'hffff_ffff_ffff_ffc0) == 0)) begin
    //          riscv_mem::fbif_err[fbif_fault_addr] = 1;
    //          `uvm_info("debug", $psprintf("inserting fbif fault for addr 0x%0x", fbif_fault_addr), UVM_HIGH);
  //      end
  //    end
  //  end
    //end
endfunction

// Insert fetch bus fault
// NEED_CHANGE
function void riscv_base_seq::insert_fetch_bus_fault(bit[63:0] pc, int code_size);
    bit [63:0] pc_pa[4];
    bit [63:0] check_fault_addr;
    bit [63:0] loop_pc;
    bit found_same_pc_pa = 0;

    // not insert error for initialization instructions
    // not insert error if there is memory access violation since it won't send to bus
  if (!m_boot_pc.exists(pc) && !m_tvec_pc.exists(pc) && pc[63:8] != min_pc[63:8] && check_mem_trans_access_violation(pc, code_size, 1, 0) == 0) begin
        for (int i=0; i<4; i++) begin
      if (i < code_size) begin
        pc_pa[i] = va2pa(pc+i, 1);
      end
      else begin
        pc_pa[i] = pc_pa[0];
      end
    end

        if (m_boot_pc.first(loop_pc))
        do begin
            for (int i=0; i<inst_arr[loop_pc].pc_pa.size(); i++) begin
        for (int j=0; j<inst_arr[loop_pc].inst_bin_code_size; j++) begin
          if ((inst_arr[loop_pc].pc_pa[i][64*j+:64]>>8) == (pc_pa[0]>>8) || 
            (inst_arr[loop_pc].pc_pa[i][64*j+:64]>>8) == (pc_pa[1]>>8) || 
            (inst_arr[loop_pc].pc_pa[i][64*j+:64]>>8) == (pc_pa[2]>>8) || 
            (inst_arr[loop_pc].pc_pa[i][64*j+:64]>>8) == (pc_pa[3]>>8)) begin
                      found_same_pc_pa = 1;
                      break;
                  end
        end
            end
        end while (m_boot_pc.next(loop_pc));

        if (m_tvec_pc.first(loop_pc))
        do begin
            for (int i=0; i<inst_arr[loop_pc].pc_pa.size(); i++) begin
        for (int j=0; j<inst_arr[loop_pc].inst_bin_code_size; j++) begin
          if ((inst_arr[loop_pc].pc_pa[i][64*j+:64]>>8) == (pc_pa[0]>>8) || 
            (inst_arr[loop_pc].pc_pa[i][64*j+:64]>>8) == (pc_pa[1]>>8) || 
            (inst_arr[loop_pc].pc_pa[i][64*j+:64]>>8) == (pc_pa[2]>>8) || 
            (inst_arr[loop_pc].pc_pa[i][64*j+:64]>>8) == (pc_pa[3]>>8)) begin
                      found_same_pc_pa = 1;
                      break;
                  end
        end
            end
        end while (m_tvec_pc.next(loop_pc));

        if (found_same_pc_pa == 0) begin
      for (int i=0; i<4; i++) begin
        //if (get_pa_range(pc_pa[i]) == PA_RANGE_IMEM) begin
              //    check_fault_addr = pc_pa[i] & 'hffff_ffff_ffff_ff00;
              //    if (!riscv_mem::tcm_tlb_err.exists(check_fault_addr)) begin
              //        if ((is_fetch_tcm_tlb_error == 1) && ($urandom % tcm_fetch_err_freq == 0)) begin
              //            riscv_mem::tcm_tlb_err[check_fault_addr] = 1;
              //      `uvm_info("debug", $psprintf("inserting ITCM fetch fault for addr 0x%0x", check_fault_addr), UVM_HIGH);
              //        end
              //    end
              //end
              //if (get_pa_range(pc_pa[i]) == PA_RANGE_EXTMEM1 || get_pa_range(pc_pa[i]) == PA_RANGE_EXTMEM2 || get_pa_range(pc_pa[i]) == PA_RANGE_EXTMEM3 || get_pa_range(pc_pa[i]) == PA_RANGE_EXTMEM4) begin
              //    check_fault_addr = pc_pa[i] & 'hffff_ffff_ffff_ffc0;
              //    if (!riscv_mem::fbif_err.exists(check_fault_addr)) begin
              //        if ((is_fetch_fbif_error == 1) && ($urandom % fbif_fetch_err_freq == 0)) begin
              //            riscv_mem::fbif_err[check_fault_addr] = 1;
              //      `uvm_info("debug", $psprintf("inserting fbif fetch fault for addr 0x%0x", check_fault_addr), UVM_HIGH);
              //        end
              //    end
              //end
      end
        end
    end
endfunction

// Check if there is instruction fetch fault exception
// NEED_CHANGE
function bit riscv_base_seq::check_fetch_fault_exception(bit[63:0] pc, int code_size);
    bit [63:0] pc_pa;
    bit [63:0] pc_pa_queue[$];
  bit [63:0] curr_pc;
    bit [63:0] check_fault_addr;
    bit has_exception = 0;

    for (int i=0; i<code_size; i++) begin
    curr_pc = pc + i;
    if (check_mem_trans_access_violation_per_byte(curr_pc, 1, 0) == 0) begin
          pc_pa = va2pa(curr_pc, 1);
            pc_pa_queue.push_back(pc_pa);

      // check fetch bus fault
        //if (get_pa_range(pc_pa) == PA_RANGE_IMEM) begin
        //    check_fault_addr = pc_pa & 'hffff_ffff_ffff_ff00;
        //    if (riscv_mem::tcm_tlb_err.exists(check_fault_addr)) begin
        //        has_exception |= riscv_mem::tcm_tlb_err[check_fault_addr];
        //    end
        //end
        //else if (get_pa_range(pc_pa) == PA_RANGE_EXTMEM1 || get_pa_range(pc_pa) == PA_RANGE_EXTMEM2 || get_pa_range(pc_pa) == PA_RANGE_EXTMEM3 || get_pa_range(pc_pa) == PA_RANGE_EXTMEM4) begin
        //    check_fault_addr = pc_pa & 'hffff_ffff_ffff_ffc0;
        //    if (riscv_mem::fbif_err.exists(check_fault_addr)) begin
        //        has_exception |= riscv_mem::fbif_err[check_fault_addr];
        //    end
        //end
      end
    else begin
      return 1;
    end
  end

  //NEED_CHANGE, check if this is needed
  //if (check_pmp_cross_boundary(pc_pa_queue) == 1) begin
  //  return 1;
  //end

    return has_exception;
endfunction

// try to get related parameter to make LSU address is in legal region
// if it's RVC instruction, then its rs1 can only be 8~15
// return 0 if success, return 1 if fail
// NEED_CHANGE
function bit riscv_base_seq::get_legal_lsu_param(inst_type_e inst_type, ref bit[4:0] rs1, ref bit[63:0] min, ref bit[63:0] max);
    bit [4:0] valid_rs1_queue[$];
    bit [63:0] min_addr_queue[$];
    bit [63:0] max_addr_queue[$];
    int idx;
    int legal_gpr_start;
    int legal_gpr_end;
  int weight;

    if (inst_type <= OP_ILLEGAL) begin
        legal_gpr_start = 1;
        legal_gpr_end = 31;
    end
    else begin // RVC inst
        legal_gpr_start = 8;
        legal_gpr_end = 15;
    end

    for (int i=legal_gpr_start; i<=legal_gpr_end; i++) begin
        if (i != reserve_gpr && i != reserve_gpr_boot && i != reserve_gpr_stack) begin
            if (0) begin
                ;
            end
//        `ifdef RISCV_PA_EXTMEM1_EXISTS
//            else if (m_gpr[i] >= `RISCV_PA_EXTMEM1_START && m_gpr[i] < `RISCV_PA_EXTMEM1_END && is_valid_clsu_base(inst_type, m_gpr[i]) == 1) begin
//        // this is fetchable region, decrease store weight for lower store modify code possibility
//        if (is_load_inst(inst_type) == 1) begin
//          weight = 1000;
//        end
//        else begin
//          weight = 100;
//        end
//
//        if ($urandom % 1000 < weight) begin
//          valid_rs1_queue.push_back(i);
//            min_addr_queue.push_back(`RISCV_PA_EXTMEM1_START);
//                  max_addr_queue.push_back(`RISCV_PA_EXTMEM1_END);
//        end
//            end
//        `endif
        end
    end

    if (valid_rs1_queue.size() == 0) begin
        return 1;
    end
    else begin
    // set some chance to not generate valid address
    if ($urandom % 100 == 0) begin
      return 1;
    end
    else begin
      idx = $urandom_range(0, valid_rs1_queue.size()-1);
          rs1 = valid_rs1_queue[idx];
          min = min_addr_queue[idx];
          max = max_addr_queue[idx];
          return 0;
    end
    end
endfunction

// check if the base is valid for corresponding C-extension LSU inst
function bit riscv_base_seq::is_valid_clsu_base(inst_type_e inst_type, bit[63:0] base);
    if ((inst_type == OP_C_LWSP || inst_type == OP_C_LW || inst_type == OP_C_SWSP || inst_type == OP_C_SW) && (base % 4 != 0)) begin
        return 0;
    end
    else if ((inst_type == OP_C_LDSP || inst_type == OP_C_LD || inst_type == OP_C_SDSP || inst_type == OP_C_SD) && (base % 8 != 0)) begin
        return 0;
    end
    else begin
        return 1;
    end
endfunction

// check if lsu store target va address has overlap with existing instructions in inst_arr[] in new random flow
function int riscv_base_seq::check_lsu_target_addr(inst_type_e inst_type, bit[63:0] addr, int bytes);
    bit [63:0] target_pc[$] = {};

    if (is_load_inst(inst_type) == 1) begin
        return 0;
    end
    else begin
        if (is_overlap_with_exist_pc(addr, bytes, 0, target_pc) == 1) begin
            return 1;
        end
        else begin
            return 0;
        end
    end
endfunction

function bit[31:0] riscv_base_seq::gen_isr_inst_code_with_pc(inst_type_e inst_type, bit[4:0] rd, bit[4:0] rs1, bit[4:0] rs2, bit[31:0] imm, bit[63:0] pc, bit[255:0] pc_pa);
    riscv_inst_base_txn tr;
    bit [ 2:0] rm;
    bit [ 4:0] rs3;

    tr = riscv_inst_base_txn::type_id::create("tr",,get_full_name());
    void'(std::randomize(rm) with { rm dist {0:/ 10, [1:4]:/ 40};});
    void'(std::randomize(rs3) with {rs3 inside {fpr_queue};});
    tr.inst_type = inst_type;
    tr.rm = rm;
    tr.rd = rd;
    tr.rs1 = rs1;
    tr.rs2 = rs2;
    tr.rs3 = rs3;
    tr.imm = imm;
    if (tr.inst_type == OP_FENCE) begin
        tr.pred = imm[7:4];
        tr.succ = imm[3:0];
    end
    else if (tr.inst_type == OP_CSRRW || tr.inst_type == OP_CSRRS || tr.inst_type == OP_CSRRC || tr.inst_type == OP_CSRRWI || tr.inst_type == OP_CSRRSI || tr.inst_type == OP_CSRRCI) begin
        tr.csr = imm[16:5];
    end
    void'(tr.gen_inst_bin_code());
    
    // extra function than generating instruction code
    // put these code in gen_isr_inst_code_with_pc() because it's only called by store_isr_inst_code()
    tr.is_key_inst = 1;
    tr.is_isr_inst = 1;
    tr.pc = pc;
    if (tr.is_in_pc_pa_queue(pc_pa) == 0) begin
        tr.pc_pa.push_back(pc_pa);
    end
  inst_arr[tr.pc] = tr;
    m_tvec_pc[tr.pc] = 1;

    return tr.inst_bin_code;
endfunction

// store M-mode ISR() instruction code into reservered memory
function void riscv_base_seq::store_isr_inst_code_with_pc(inst_type_e inst_type, bit[4:0] rd, bit[4:0] rs1, bit[4:0] rs2, bit[31:0] imm, bit[63:0] pc);
    bit [31:0] inst_code;
    bit [255:0] pc_pa;
    bit [63:0] branch_pc;
    int inst_code_size;

  inst_code_size = get_fetch_size(inst_type);

    pc_pa = 0;
  for (int i=0; i<inst_code_size; i++) begin
    pc_pa[64*i+:64] = pc+i;  // M-mode is always bare
  end
    inst_code = gen_isr_inst_code_with_pc(inst_type, rd, rs1, rs2, imm, pc, pc_pa);

    for (int i=0; i<inst_code_size; i++) begin
        riscv_mem::dut_mem[pc_pa[64*i+:64]] = inst_code[8*i+:8];
        riscv_mem::rm_mem[pc_pa[64*i+:64]] = inst_code[8*i+:8];
        m_mem[pc_pa[64*i+:64]] = inst_code[8*i+:8];
        m_init_mem[pc_pa[64*i+:64]] = inst_code[8*i+:8];
    end

    // prepare instruction in branch target also when big branch is enabled in trap handler
    if (trap_pc_offset != 0) begin
        branch_pc = pc + trap_pc_offset;
    pc_pa = 0;
        for (int i=0; i<inst_code_size; i++) begin
      pc_pa[64*i+:64] = branch_pc+i;
    end
        inst_code = gen_isr_inst_code_with_pc(inst_type, rd, rs1, rs2, imm, branch_pc, pc_pa);

        for (int i=0; i<inst_code_size; i++) begin
            riscv_mem::dut_mem[pc_pa[64*i+:64]] = inst_code[8*i+:8];
            riscv_mem::rm_mem[pc_pa[64*i+:64]] = inst_code[8*i+:8];
            m_mem[pc_pa[64*i+:64]] = inst_code[8*i+:8];
            m_init_mem[pc_pa[64*i+:64]] = inst_code[8*i+:8];
        end
    end
endfunction: store_isr_inst_code_with_pc

// store S-mode ISR() instruction code into reservered memory
function void riscv_base_seq::store_smode_isr_inst_code_with_pc(inst_type_e inst_type, bit[4:0] rd, bit[4:0] rs1, bit[4:0] rs2, bit[31:0] imm, bit[63:0] pc);
    bit [31:0] inst_code;
    bit [255:0] pc_pa;
    bit [63:0] branch_pc;
    bit [255:0] branch_pc_pa;
    privilege_level_e ori_priv_level;
    int inst_code_size;

    branch_pc = pc + trap_pc_offset_smode;
  inst_code_size = get_fetch_size(inst_type);

    // calculate PA
    ori_priv_level = m_curr_priv_level;  // save original
    m_curr_priv_level = PRIV_LEVEL_SMODE;
    for (int i=0; i<inst_code_size; i++) begin
    pc_pa[64*i+:64] = va2pa(pc+i, 1);
      branch_pc_pa[64*i+:64] = va2pa(branch_pc+i, 1);
  end
    m_curr_priv_level = ori_priv_level;  // restore

    inst_code = gen_isr_inst_code_with_pc(inst_type, rd, rs1, rs2, imm, pc, pc_pa);
    for (int i=0; i<inst_code_size; i++) begin
        riscv_mem::dut_mem[pc_pa[64*i+:64]] = inst_code[8*i+:8];
        riscv_mem::rm_mem[pc_pa[64*i+:64]] = inst_code[8*i+:8];
        m_mem[pc_pa[64*i+:64]] = inst_code[8*i+:8];
        m_init_mem[pc_pa[64*i+:64]] = inst_code[8*i+:8];
    end

    // prepare instruction in branch target also when big branch is enabled in trap handler
    if (trap_pc_offset_smode != 0) begin
        pc_pa = branch_pc_pa;
        inst_code = gen_isr_inst_code_with_pc(inst_type, rd, rs1, rs2, imm, branch_pc, pc_pa);
        for (int i=0; i<inst_code_size; i++) begin
            riscv_mem::dut_mem[pc_pa[64*i+:64]] = inst_code[8*i+:8];
            riscv_mem::rm_mem[pc_pa[64*i+:64]] = inst_code[8*i+:8];
            m_mem[pc_pa[64*i+:64]] = inst_code[8*i+:8];
            m_init_mem[pc_pa[64*i+:64]] = inst_code[8*i+:8];
        end
    end
endfunction: store_smode_isr_inst_code_with_pc

// store M-mode ISR() instruction code into reservered memory
task riscv_base_seq::store_isr_inst_code(inst_type_e inst_type, bit[4:0] rd, bit[4:0] rs1, bit[4:0] rs2, bit[31:0] imm);
    bit [31:0] inst_code;
    bit [255:0] pc_pa;
    int inst_code_size;

  inst_code_size = get_fetch_size(inst_type);

    for (int i=0; i<inst_code_size; i++) begin
    pc_pa[64*i+:64] = curr_mmode_isr_addr+i;  // M-mode is always bare
  end
    inst_code = gen_isr_inst_code_with_pc(inst_type, rd, rs1, rs2, imm, curr_mmode_isr_addr, pc_pa);

    for (int i=0; i<inst_code_size; i++) begin
        riscv_mem::dut_mem[pc_pa[64*i+:64]] = inst_code[8*i+:8];
        riscv_mem::rm_mem[pc_pa[64*i+:64]] = inst_code[8*i+:8];
        m_mem[pc_pa[64*i+:64]] = inst_code[8*i+:8];
        m_init_mem[pc_pa[64*i+:64]] = inst_code[8*i+:8];
    end

    curr_mmode_isr_addr += inst_code_size;
endtask

// store S-mode ISR() instruction code into reservered memory
task riscv_base_seq::store_smode_isr_inst_code(inst_type_e inst_type, bit[4:0] rd, bit[4:0] rs1, bit[4:0] rs2, bit[31:0] imm);
    bit [31:0] inst_code;
    bit [255:0] pc_pa;
    privilege_level_e ori_priv_level;
    int inst_code_size;

  inst_code_size = get_fetch_size(inst_type);

    ori_priv_level = m_curr_priv_level;  // save original
    m_curr_priv_level = PRIV_LEVEL_SMODE;  // S-mode ISR must run in S-mode
    for (int i=0; i<inst_code_size; i++) begin
    pc_pa[64*i+:64] = va2pa(curr_smode_isr_addr+i, 1);
  end
    m_curr_priv_level = ori_priv_level;  // restore
    inst_code = gen_isr_inst_code_with_pc(inst_type, rd, rs1, rs2, imm, curr_smode_isr_addr, pc_pa);

    for (int i=0; i<inst_code_size; i++) begin
        riscv_mem::dut_mem[pc_pa[64*i+:64]] = inst_code[8*i+:8];
        riscv_mem::rm_mem[pc_pa[64*i+:64]] = inst_code[8*i+:8];
        m_mem[pc_pa[64*i+:64]] = inst_code[8*i+:8];
        m_init_mem[pc_pa[64*i+:64]] = inst_code[8*i+:8];
    end

    curr_smode_isr_addr += inst_code_size;
endtask

task riscv_base_seq::create_op(inst_type_e inst_type, bit[4:0] rd, bit[4:0] rs1, bit[4:0] rs2, bit[31:0] imm, bit is_key_inst,int rs3);
  riscv_inst_base_txn tr;
    bit [255:0] pa;
    bit [ 2:0] rm;

  tr = riscv_inst_base_txn::type_id::create("tr",,get_full_name());
  //start_item(tr);
    void'(std::randomize(rm) with { rm dist {0:/ 20, [1:4]:/ 80, [5:6]:/ 2, 7:/ 3};});
    if(rs3 == -1)begin void'(std::randomize(rs3) with {rs3 inside {fpr_queue};}); end
  tr.rm        = rm;
  tr.rd        = rd;
  tr.rs1       = rs1;
  tr.rs2       = rs2;
  tr.rs3       = rs3;
  tr.imm       = imm;
    tr.inst_type = inst_type;

    if (tr.inst_type == OP_FENCE) begin
        tr.pred = imm[7:4];
        tr.succ = imm[3:0];
    end
    else if (tr.inst_type == OP_CSRRW || tr.inst_type == OP_CSRRS || tr.inst_type == OP_CSRRC || tr.inst_type == OP_CSRRWI || tr.inst_type == OP_CSRRSI || tr.inst_type == OP_CSRRCI) begin
        tr.csr = imm[16:5];
    end
  void'(tr.gen_inst_bin_code());
  tr.pc = m_curr_pc;
  tr.is_key_inst = is_key_inst;
    
  for (int i=0; i<tr.inst_bin_code_size; i++) begin
      pa[64*i+:64] = va2pa(tr.pc+i, 1);
  end

    if (tr.is_in_pc_pa_queue(pa) == 0) begin
        tr.pc_pa.push_back(pa);
    end

  inst_arr[tr.pc] = tr;
  `uvm_info("OP_DUMP1", $psprintf("generated one instruction transaction:\n%s", tr.sprint()), UVM_MEDIUM);
    if (tr.inst_type <= OP_ILLEGAL) begin
        m_curr_pc += 4;
    end
    else begin  //C-extension
        m_curr_pc += 2;
    end
    riscv_inst_base_txn::instn +=1;
    //finish_item(tr);
    store_inst_code(tr);
endtask

// different task than create_op()
// In this task, pc is passed through parameter. And op is not stored into inst_arr because it had been done before
task riscv_base_seq::create_op_with_pc(inst_type_e inst_type, bit[4:0] rd, bit[4:0] rs1, bit[4:0] rs2, bit[31:0] imm, bit[63:0] pc, int rs3);
  riscv_inst_base_txn tr;
    bit [255:0] pa;
    bit [ 2:0] rm;

  tr = riscv_inst_base_txn::type_id::create("tr",,get_full_name());
  //start_item(tr);
    void'(std::randomize(rm) with { rm dist {0:/ 20, [1:4]:/ 60, [5:6]:/ 3, 7:/ 20};});
    if(rs3 == -1)begin void'(std::randomize(rs3) with {rs3 inside {fpr_queue};}); end
  tr.rm = rm;
    tr.inst_type = inst_type;
  tr.rd = rd;
  tr.rs1 = rs1;
  tr.rs2 = rs2;
  tr.rs3 = rs3;
  tr.imm = imm;
  tr.pc = pc;
  void'(tr.gen_inst_bin_code());
    
  for (int i=0; i<tr.inst_bin_code_size; i++) begin
      pa[64*i+:64] = va2pa(tr.pc+i, 1);
  end

    if (tr.is_in_pc_pa_queue(pa) == 0) begin
        tr.pc_pa.push_back(pa);
    end

  `uvm_info("OP_DUMP3", $psprintf("generated one instruction transaction:\n%s", tr.sprint()), UVM_MEDIUM);
    //finish_item(tr);
    store_inst_code(tr);
endtask

task riscv_base_seq::init_random_gpr();
    gen_init_gpr();
    init_gpr();
endtask

task riscv_base_seq::create_op_init_reserve_gpr(bit[4:0] dest_gpr, bit[63:0] wdata, bit[4:0] tmp_gpr, bit[4:0] tmp_gpr_1);
    create_op(OP_ADDI, tmp_gpr, 0, 0, wdata[11:0], 1);
    create_op(OP_SLLI, tmp_gpr, tmp_gpr, 0, 52, 1);
    create_op(OP_SRLI, tmp_gpr, tmp_gpr, 0, 52, 1);
    create_op(OP_LUI, tmp_gpr_1, 0, 0, wdata[31:0], 1);
    create_op(OP_SLLI, tmp_gpr_1, tmp_gpr_1, 0, 32, 1);
    create_op(OP_SRLI, tmp_gpr_1, tmp_gpr_1, 0, 32, 1);
    create_op(OP_ADD, dest_gpr, tmp_gpr, tmp_gpr_1, 0, 1);
    create_op(OP_ADDI, tmp_gpr, 0, 0, wdata[43:32], 1);
    create_op(OP_SLLI, tmp_gpr, tmp_gpr, 0, 52, 1);
    create_op(OP_SRLI, tmp_gpr, tmp_gpr, 0, 52, 1);
    create_op(OP_LUI, tmp_gpr_1, 0, 0, wdata[63:32], 1);
    create_op(OP_SLLI, tmp_gpr_1, tmp_gpr_1, 0, 32, 1);
    create_op(OP_SRLI, tmp_gpr_1, tmp_gpr_1, 0, 32, 1);
    create_op(OP_ADD, tmp_gpr, tmp_gpr, tmp_gpr_1, 0, 1);
    create_op(OP_SLLI, tmp_gpr, tmp_gpr, 0, 32, 1);
    create_op(OP_ADD, dest_gpr, tmp_gpr, dest_gpr, 0, 1);
endtask

// initialize all reserved GPR with pre-defined memory base value
task riscv_base_seq::init_all_reserve_gpr();
    bit [4:0] tmp_gpr;
    bit [4:0] tmp_gpr_1;
  bit [63:0] wdata;

  for (int i=1; i<32; i++) begin
        if (!rsvd_gpr_arr.exists(i)) begin
            tmp_gpr = i;
            break;
        end
    end

    for (int i=1; i<32; i++) begin
        if (!rsvd_gpr_arr.exists(i) && i != tmp_gpr) begin
            tmp_gpr_1 = i;
            break;
        end
    end

    create_op_init_reserve_gpr(reserve_gpr, reserve_mem_start_va, tmp_gpr, tmp_gpr_1);
    create_op_init_reserve_gpr(reserve_gpr_boot, init_start_pc, tmp_gpr, tmp_gpr_1);
    create_op_init_reserve_gpr(reserve_gpr_stack, stack_start_va, tmp_gpr, tmp_gpr_1);
    create_op_init_reserve_gpr(reserve_gpr_iaf_step, reserve_gpr_iaf_step_wdata, tmp_gpr, tmp_gpr_1);
    create_op_init_reserve_gpr(reserve_gpr_iaf_offset, 0, tmp_gpr, tmp_gpr_1);
endtask


// initial gpr value is generated before calling this function
task riscv_base_seq::init_gpr();
    for (int i=1; i<32; i++) begin
        if (!rsvd_gpr_arr.exists(i)) begin
            create_op_ld_gpr(i, c_gpr.gpr[i-1]);
        end
    end
endtask

// initialize fpr
task riscv_base_seq::init_fpr(int cnt);
    bit [4:0] tmp_gpr;
    bit [63:0] wdata;

    tmp_gpr = get_random_non_zero_gpr();

    // save tmp_gpr
    create_op(OP_CSRRW, 0, tmp_gpr, 0, (`CSR_MSCRATCH << 5));

    //init fpr
    wdata = gen_fp_data();
    for (int i=0; i<32; i++) begin
      if($urandom %40 ==0 || cnt == 0 || i inside {fpr_queue})begin
        void'(std::randomize(rnd3) with { rnd3 dist {0:/ 30, 1:/50, 2:/20};});
        if(rnd3 == 0)begin//gen new fp data
          wdata = gen_fp_data();
        end else if(rnd3 == 1)begin//gen new fp data with delta
          wdata = fp_data_delta(wdata);
        end else begin//keep fp data
        end
        create_op_ld_gpr(tmp_gpr, wdata);
        create_op(OP_FMV_S_X, i, tmp_gpr, 0, 0);
        `uvm_info("INIT_FPR_DUMP", $psprintf("Initial randomized fpr[%2d] = %8x with gpr:%2d\n", i, wdata[31:0],tmp_gpr), UVM_HIGH);
        end
    end

    //randomize fs
    void'(std::randomize(fs) with {fs dist {0 :/ 1, 1 :/ 50, 2 :/ 50, 3 :/ 2};});

    `uvm_info("set_fs", $psprintf("fs:%0d",fs), UVM_HIGH);
    wdata = fs <<13;
    create_op_ld_gpr(tmp_gpr, wdata);
    create_op(OP_CSRRS, 0, tmp_gpr, 0, (`CSR_MSTATUS <<5));//set mstatus.fs

    wdata = (~fs & 3) <<13;
    create_op_ld_gpr(tmp_gpr, wdata);
    create_op(OP_CSRRC, 0, tmp_gpr, 0, (`CSR_MSTATUS <<5));//clear mstatus.fs


    // restore tmp_gpr
    create_op(OP_CSRRW, tmp_gpr, 0, 0, (`CSR_MSCRATCH << 5));
endtask

// initialize fcsr
task riscv_base_seq::init_fcsr();
    bit [4:0] tmp_gpr;
    bit [63:0] wdata;

    tmp_gpr = get_random_non_zero_gpr();

    // save tmp_gpr
    create_op(OP_CSRRW, 0, tmp_gpr, 0, (`CSR_MSCRATCH << 5));

    //init fcsr.rm
    wdata = {$urandom, $urandom};
    void'(std::randomize(frm) with { frm dist {0:/ 40, [1:4]:/50, [5:7]:/3};});
    wdata[7:5] = frm;
    create_op_ld_gpr(tmp_gpr, wdata);
    create_op(OP_CSRRW, 0, tmp_gpr, 0, (`CSR_FCSR <<5));//write fscr
    create_op(OP_CSRRS, tmp_gpr, 0, 0, (`CSR_FCSR <<5));//read fcsr for check

    // restore tmp_gpr
    create_op(OP_CSRRW, tmp_gpr, 0, 0, (`CSR_MSCRATCH << 5));
endtask

// create operation to load pre-defined value (stored in reserve memory) into specified gpr
task riscv_base_seq::create_op_ld_gpr(bit[4:0] gpr, bit[63:0] value);
    bit [63:0] addr;

    // all lsu imm-12 has been used up, need to update reserve memory base
    if (reserve_offset == 'h800) begin
        reserve_offset = 0;
        reserve_mem_start_va = reserve_mem_start_va + 'h1000;
        create_op(OP_ADDI, reserve_gpr, reserve_gpr, 0, 'h700, 1);
        create_op(OP_ADDI, reserve_gpr, reserve_gpr, 0, 'h700, 1);
        create_op(OP_ADDI, reserve_gpr, reserve_gpr, 0, 'h200, 1);
    end

    // store pre-defined value into reserve memory
    reserve_mem_start_pa = va2pa(reserve_mem_start_va, 0);
    addr = reserve_mem_start_pa + signed'(sign_extend(reserve_offset, 12));
    `uvm_info("debug", $psprintf("addr=%h, value=%h, reserve_gpr=%0d, reserve_offset=%h", addr, value,reserve_gpr,reserve_offset), UVM_HIGH)
    for (int i=0; i<8; i++) begin
    riscv_mem::dut_mem[addr+i] = value[8*i+:8];
    riscv_mem::rm_mem[addr+i] = value[8*i+:8];
    m_mem[addr+i] = value[8*i+:8];
    m_init_mem[addr+i] = value[8*i+:8];
    end

    // create operation to load into specified gpr
    create_op(OP_LD, gpr, reserve_gpr, 0, reserve_offset, 1);

  reserve_offset += 8;
endtask

// NEED_CHANGE
task riscv_base_seq::config_pmp_region();
    bit [63:0] wdata;
    bit [63:0] wdata_cfg=0;
    bit [4:0] tmp_gpr;
  bit [4:0] rd;
    int j;

  for (int i=1; i<32; i++) begin
        if (!rsvd_gpr_arr.exists(i)) begin
            tmp_gpr = i;
            break;
        end
    end

    do begin
        rd = $urandom_range(0, 31);
    end while (rd == tmp_gpr || rsvd_gpr_arr.exists(rd));

    for (int i=0; i<`MAX_PMP_NUM; i++) begin
        j = i%8;
        wdata = m_init_pmpaddr_cfg[i].paddr;
        create_op_ld_gpr(tmp_gpr, wdata);
        create_op(OP_CSRRW, rd, tmp_gpr, 0, ((`CSR_PMPADDR0 + i)<< 5), 1);
        wdata_cfg[(j+1)*8-1 -:8] =  m_init_pmpcfg_cfg[i].pack_cfg();
        if(i==7) begin
            `uvm_info("debug", $psprintf("wdata_cfg=0x%0x, tmp_gpr=%d", wdata_cfg, tmp_gpr), UVM_HIGH);
            create_op_ld_gpr(tmp_gpr, wdata_cfg);
            create_op(OP_CSRRW, rd, tmp_gpr, 0, ((`CSR_PMPCFG0)<< 5), 1);
            wdata_cfg = 0;
        end
        else if(i==15) begin
            `uvm_info("debug", $psprintf("wdata_cfg=0x%0x, tmp_gpr=%d", wdata_cfg, tmp_gpr), UVM_HIGH);
            create_op_ld_gpr(tmp_gpr, wdata_cfg);
            create_op(OP_CSRRW, rd, tmp_gpr, 0, ((`CSR_PMPCFG2)<< 5), 1);
            wdata_cfg = 0;
        end
    end
endtask

// write mtvec CSR to configure trap vector
task riscv_base_seq::config_trap_vector();
    bit [4:0] tmp_gpr;
  bit [4:0] rd;
    bit [63:0] wdata;

    for (int i=1; i<32; i++) begin
        if (!rsvd_gpr_arr.exists(i)) begin
            tmp_gpr = i;
            break;
        end
    end

  rd = 0;

    wdata[`RISCV_CSR_MTVEC_BASE] = m_init_mmode_trap_vector[`RISCV_CSR_MTVEC_BASE];
    wdata[`RISCV_CSR_MTVEC_MODE] = mtvec_mode;
  create_op_ld_gpr(tmp_gpr, wdata);
    create_op(OP_CSRRW, rd, tmp_gpr, 0, (`CSR_MTVEC << 5), 1);
    `uvm_info("debug", $psprintf("write MTVEC base = 0x%x, mode = %0d", m_init_mmode_trap_vector, mtvec_mode), UVM_HIGH);
    wdata[`RISCV_CSR_STVEC_BASE] = m_init_smode_trap_vector[`RISCV_CSR_STVEC_BASE];
    wdata[`RISCV_CSR_STVEC_MODE] = stvec_mode;
    create_op_ld_gpr(tmp_gpr, wdata);
    create_op(OP_CSRRW, rd, tmp_gpr, 0, (`CSR_STVEC << 5), 1);
    `uvm_info("debug", $psprintf("write STVEC base = 0x%x, mode = %0d", m_init_smode_trap_vector, stvec_mode), UVM_HIGH);
endtask


// configure correspnding interrupt enable
// NEED_CHANGE
task riscv_base_seq::config_interrupt_en();
    bit [4:0] tmp_gpr;
  bit [4:0] rd;
    bit [31:0] imm;
    bit [63:0] offset;
    bit [63:0] wdata;
    bit status_mie;
    bit status_sie;
    bit ie_msie;
    bit ie_mtie;
    bit ie_meie;
    bit ie_ssie;
    bit ie_stie;
    bit ie_seie;

    for (int i=1; i<32; i++) begin
        if (!rsvd_gpr_arr.exists(i)) begin
            tmp_gpr = i;
            break;
        end
    end

  rd = 0;

    if (interrupt_en == 1) begin
        if (interrupt_must_en == 1) begin  //used for wfi case
            status_mie = $urandom;
            ie_msie = $urandom;
            ie_mtie = $urandom;
            ie_meie = $urandom;
            if (dis_smode == 0) begin
                status_sie = $urandom;
                ie_ssie = $urandom;
                ie_stie = $urandom;
                ie_seie = $urandom;
            end

      while (ie_mtie == 0 && 
                   ie_meie == 0 &&
           ie_msie == 0 && 
                   // for S software/timer interrupt, it's triggered by ucode csr writing, can't depend on them for wfi wakeup
                   ie_seie == 0) begin
        ie_msie = $urandom;
              ie_mtie = $urandom;
              ie_meie = $urandom;
                if (dis_smode == 0) begin
                    ie_ssie = $urandom;
                    ie_stie = $urandom;
                    ie_seie = $urandom;
                end
      end
        end
        else begin
            status_mie = (($urandom%4)==0) ? 0 : 1;
            ie_msie = (($urandom%4)==0) ? 0 : 1;
            ie_mtie = (($urandom%4)==0) ? 0 : 1;
            ie_meie = (($urandom%4)==0) ? 0 : 1;
            if (dis_smode == 0) begin
                status_sie = (($urandom%4)==0) ? 0 : 1;
                ie_ssie = (($urandom%4)==0) ? 0 : 1;
                ie_stie = (($urandom%4)==0) ? 0 : 1;
                ie_seie = (($urandom%4)==0) ? 0 : 1;
            end
        end
    end
    else begin
        status_mie = (($urandom%3)==0) ? 0 : 1;
        if (dis_smode == 0) status_sie = (($urandom%3)==0) ? 0 : 1;
        ie_msie = (($urandom%3)==0) ? 1 : 0;
        ie_mtie = (($urandom%3)==0) ? 1 : 0;
        ie_meie = (($urandom%3)==0) ? 1 : 0;
        if (dis_smode == 0) begin
            ie_ssie = (($urandom%3)==0) ? 1 : 0;
            ie_stie = (($urandom%3)==0) ? 1 : 0;
            ie_seie = (($urandom%3)==0) ? 1 : 0;
        end
    end

    `uvm_info("debug", $psprintf("interrupt enable config: status_mie = %0d, ie_msie = %0d, ie_mtie = %0d, ie_meie = %0d", status_mie, ie_msie, ie_mtie, ie_meie), UVM_NONE);
    if (dis_smode == 0) begin
        `uvm_info("debug", $psprintf("interrupt enable config: status_sie = %0d, ie_ssie = %0d, ie_stie = %0d, ie_seie = %0d", status_sie, ie_ssie, ie_stie, ie_seie), UVM_NONE);
    end

    // configure mie
    imm[16:5] = `CSR_MSTATUS;
    imm[`RISCV_CSR_MSTATUS_MIE] = status_mie;
    create_op(OP_CSRRSI, rd, 0, 0, imm);

    // configure sie
    if (dis_smode == 0) begin
        imm[16:5] = (($urandom%2)==0) ? `CSR_MSTATUS : `CSR_SSTATUS;
        imm[`RISCV_CSR_MSTATUS_SIE] = status_sie;
        create_op(OP_CSRRSI, rd, 0, 0, imm);
    end

    // save tmp_gpr
    create_op(OP_CSRRW, 0, tmp_gpr, 0, (`CSR_MSCRATCH << 5));

    // configure msie/mtie/meie
    wdata[`RISCV_CSR_MIE_MSIE] = ie_msie;
    wdata[`RISCV_CSR_MIE_MTIE] = ie_mtie;
    wdata[`RISCV_CSR_MIE_MEIE] = ie_meie;
    create_op_ld_gpr(tmp_gpr, wdata);
    create_op(OP_CSRRS, rd, tmp_gpr, 0, (`CSR_MIE << 5));

    // configure ssie/stie/seie
    if (dis_smode == 0) begin
        wdata[`RISCV_CSR_MIE_SSIE] = ie_ssie;
        wdata[`RISCV_CSR_MIE_STIE] = ie_stie;
        wdata[`RISCV_CSR_MIE_SEIE] = ie_seie;
        create_op_ld_gpr(tmp_gpr, wdata);
        create_op(OP_CSRRS, rd, tmp_gpr, 0, (`CSR_MIE << 5));
    end

    // restore tmp_gpr
    create_op(OP_CSRRW, tmp_gpr, 0, 0, (`CSR_MSCRATCH << 5));
endtask

// config to run in user mode or machine mode
task riscv_base_seq::config_riscv_mode();
    bit [4:0] tmp_gpr;
  bit [4:0] rd;
    privilege_level_e mode;
    bit [63:0] wdata;

    if (dis_mmode == 0) begin
        if (dis_usmode == 0) begin
            if (dis_smode == 0) begin
                void'(std::randomize(mode) with {
                    mode dist {PRIV_LEVEL_MMODE:/1, PRIV_LEVEL_SMODE:/2, PRIV_LEVEL_UMODE:/2};
                });
            end
            else begin
                void'(std::randomize(mode) with {
                    mode dist {PRIV_LEVEL_MMODE:/1, PRIV_LEVEL_UMODE:/2};
                });
            end
        end
        else begin
            mode = PRIV_LEVEL_MMODE;
        end
    end
    else begin
        if (dis_smode == 1) begin
            mode = PRIV_LEVEL_UMODE;
        end
        else begin
            void'(std::randomize(mode) with {
                mode dist {PRIV_LEVEL_SMODE:/1, PRIV_LEVEL_UMODE:/1};
            });
        end
    end

    for (int i=1; i<32; i++) begin
        if (!rsvd_gpr_arr.exists(i)) begin
            tmp_gpr = i;
            break;
        end
    end

  rd = 0;

    if (mode == PRIV_LEVEL_UMODE) begin
        `uvm_info("MODE", $psprintf("enter umode"), UVM_NONE);
        // save tmp_gpr
        create_op(OP_CSRRW, 0, tmp_gpr, 0, (`CSR_MSCRATCH << 5));

    wdata = 0;
    wdata[`RISCV_CSR_MSTATUS_MPP] = 2'b11;
        create_op_ld_gpr(tmp_gpr, wdata);
        create_op(OP_CSRRC, rd, tmp_gpr, 0, (`CSR_MSTATUS << 5));
        create_op(OP_AUIPC, tmp_gpr, 0, 0, 0);
        create_op(OP_ADDI, tmp_gpr, tmp_gpr, 0, 20);
        create_op(OP_CSRRW, 0, tmp_gpr, 0, (`CSR_MEPC << 5));

        // restore tmp_gpr
        create_op(OP_CSRRW, tmp_gpr, 0, 0, (`CSR_MSCRATCH << 5));

        create_op(OP_MRET, 0, 0, 0, 0);
        m_curr_priv_level = PRIV_LEVEL_UMODE;
    end
    else if (mode == PRIV_LEVEL_SMODE) begin
        `uvm_info("MODE", $psprintf("enter smode"), UVM_NONE);
        // save tmp_gpr
        create_op(OP_CSRRW, 0, tmp_gpr, 0, (`CSR_MSCRATCH << 5));

    wdata = 0;
    wdata[`RISCV_CSR_MSTATUS_MPP] = 2'b01;
    create_op_ld_gpr(tmp_gpr, wdata);
        create_op(OP_CSRRS, rd, tmp_gpr, 0, (`CSR_MSTATUS << 5));  //set mstatus.mpp[0]
    wdata = 0;
    wdata[`RISCV_CSR_MSTATUS_MPP] = 2'b10;
    create_op_ld_gpr(tmp_gpr, wdata);
        create_op(OP_CSRRC, rd, tmp_gpr, 0, (`CSR_MSTATUS << 5));  //clear mstatus.mpp[1]
        create_op(OP_AUIPC, tmp_gpr, 0, 0, 0);
        create_op(OP_ADDI, tmp_gpr, tmp_gpr, 0, 20);
        create_op(OP_CSRRW, 0, tmp_gpr, 0, (`CSR_MEPC << 5));

        // restore tmp_gpr
        create_op(OP_CSRRW, tmp_gpr, 0, 0, (`CSR_MSCRATCH << 5));

        create_op(OP_MRET, 0, 0, 0, 0);
        m_curr_priv_level = PRIV_LEVEL_SMODE;
    end else begin
        `uvm_info("MODE", $psprintf("keep mmode"), UVM_NONE);
    end
endtask

task riscv_base_seq::config_mtimecmp();
    bit [4:0] tmp_gpr;
  bit [4:0] rd;
  bit [63:0] wdata;

    for (int i=1; i<32; i++) begin
        if (!rsvd_gpr_arr.exists(i)) begin
            tmp_gpr = i;
            break;
        end
    end

  rd = 0;

    // save tmp_gpr
    create_op(OP_CSRRW, 0, tmp_gpr, 0, (`CSR_MSCRATCH << 5));

    if (interrupt_en == 1) begin
    if (init_timecmp != 0) begin
      wdata = init_timecmp;
    end
    else begin
      wdata = $urandom_range('h1, 'h1000);
    end
  end
  else begin
    wdata = 'hffff_ffff_ffff_ffff;
  end

  create_op_ld_gpr(tmp_gpr, wdata);
    create_op(OP_CSRRW, rd, tmp_gpr, 0, (`CSR_MTIMECMP << 5));

    // restore tmp_gpr
    create_op(OP_CSRRW, tmp_gpr, 0, 0, (`CSR_MSCRATCH << 5));
endtask

task riscv_base_seq::config_delegation();
    bit [4:0] tmp_gpr;
  bit [4:0] rd;
  bit [63:0] wdata;

    for (int i=1; i<32; i++) begin
        if (!rsvd_gpr_arr.exists(i)) begin
            tmp_gpr = i;
            break;
        end
    end

  rd = 0;

    // when dis_smode = 1, keep delegation to reset value to avoid trap to S-mode
    if (dis_smode == 0) begin
        // save tmp_gpr
        create_op(OP_CSRRW, 0, tmp_gpr, 0, (`CSR_MSCRATCH << 5));

        wdata = {$urandom, $urandom};
      create_op_ld_gpr(tmp_gpr, wdata);
        create_op(OP_CSRRW, rd, tmp_gpr, 0, (`CSR_MEDELEG << 5));
        wdata = {$urandom, $urandom};
      create_op_ld_gpr(tmp_gpr, wdata);
        create_op(OP_CSRRW, rd, tmp_gpr, 0, (`CSR_MIDELEG << 5));
        mideleg[`RISCV_CSR_MIDELEG_SSID] = wdata[`RISCV_CSR_MIDELEG_SSID];
        mideleg[`RISCV_CSR_MIDELEG_STID] = wdata[`RISCV_CSR_MIDELEG_STID];
        mideleg[`RISCV_CSR_MIDELEG_SEID] = wdata[`RISCV_CSR_MIDELEG_SEID];

        // restore tmp_gpr
        create_op(OP_CSRRW, tmp_gpr, 0, 0, (`CSR_MSCRATCH << 5));
    end
endtask

// configure core pmp
// NEED_CHANGE
task riscv_base_seq::init_pmp_cfg();

    pmpaddr_cfg pmpaddr_cfg_txn ;
    pmpcfg_cfg  pmpcfg_cfg_txn  ;

//`ifdef RISCV_PA_EXTMEM1_EXISTS
//    set_pmp_region(`RISCV_PA_EXTMEM1_START, `RISCV_PA_EXTMEM1_END);
//`endif

foreach(m_used_pmp_idx[i] ) begin
    `uvm_info("init_pmp_cfg", $psprintf("m_used_pmp_idx[%d]=%d", i, m_used_pmp_idx[i]), UVM_HIGH)
end
    for (int i=0; i<`MAX_PMP_NUM ; i++) begin
        if (!m_used_pmp_idx.exists(i)) begin
            pmpaddr_cfg_txn = new();
            pmpcfg_cfg_txn  = new();
            pmpcfg_cfg_txn.r = 1;
            pmpcfg_cfg_txn.w = 1;
            pmpcfg_cfg_txn.x = 1;
            pmpcfg_cfg_txn.a = 0;
            pmpcfg_cfg_txn.s = 1;
            pmpcfg_cfg_txn.l = 1;
            void'(pmpcfg_cfg_txn.pack_cfg());
            pmpaddr_cfg_txn.paddr = 0;
            m_init_pmpaddr_cfg[i] = pmpaddr_cfg_txn;
            m_init_pmpcfg_cfg[i]  = pmpcfg_cfg_txn;
            m_used_pmp_idx[i] = 1;
        end
    end
    if(m_init_pmpcfg_cfg[0].a == `PMP_TOR)  m_init_pmpaddr_cfg[0].min_addr = 0;
    for (int i=0; i<`MAX_PMP_NUM; i++) begin
        `uvm_info("debug", $psprintf("\nFor pmp region %2d: pmpaddr = 0x%16x, range = 0x%16x, base = 0x%16x, pmpcfg = %2x, pmpcfg.r = %2d, pmpcfg.w = %2d, pmpcfg.x = %2d, pmpcfg.a = %2d, pmpcfg.s = %2d, pmpcfg.l = %2d", i, m_init_pmpaddr_cfg[i].paddr, m_init_pmpaddr_cfg[i].range, m_init_pmpaddr_cfg[i].min_addr,  m_init_pmpcfg_cfg[i].value , m_init_pmpcfg_cfg[i].r, m_init_pmpcfg_cfg[i].w, m_init_pmpcfg_cfg[i].x, m_init_pmpcfg_cfg[i].a, m_init_pmpcfg_cfg[i].s, m_init_pmpcfg_cfg[i].l), UVM_HIGH);
    end
endtask

task riscv_base_seq::config_mcounteren();
    bit [4:0] tmp_gpr;
  bit [4:0] rd;
  bit [63:0] wdata;

    for (int i=1; i<32; i++) begin
        if (!rsvd_gpr_arr.exists(i)) begin
            tmp_gpr = i;
            break;
        end
    end

  rd = 0;

    wdata = {$urandom, $urandom};
  create_op_ld_gpr(tmp_gpr, wdata);
    create_op(OP_CSRRW, rd, tmp_gpr, 0, (`CSR_MCOUNTEREN << 5), 1);
    wdata = {$urandom, $urandom};
  create_op_ld_gpr(tmp_gpr, wdata);
    create_op(OP_CSRRW, rd, tmp_gpr, 0, (`CSR_SCOUNTEREN << 5), 1);
endtask

task riscv_base_seq::config_mstatus();
    bit [4:0] tmp_gpr;
  bit [4:0] rd;
  bit [63:0] wdata;

    for (int i=1; i<32; i++) begin
        if (!rsvd_gpr_arr.exists(i)) begin
            tmp_gpr = i;
            break;
        end
    end

  rd = 0;

    wdata = {$urandom, $urandom};

    // when enable interrupt, leaving trap handler will set mpp/spp to 0
    // This can't be predicted by TB, so must set mpp/spp to 0
    if (interrupt_en == 1) begin
        wdata[`RISCV_CSR_MSTATUS_MPP] = 0;
        wdata[`RISCV_CSR_MSTATUS_SPP] = 0;
    end
    else begin
      wdata[`RISCV_CSR_MSTATUS_MPP] = (($urandom%3)==0) ? 0 : (($urandom%2) ? 1 : 3);
      wdata[`RISCV_CSR_MSTATUS_SPP] = ($urandom%2) ? 0 : 1;
    end

    void'(std::randomize(fs) with {fs dist {1 :/ 50, 2 :/ 50, 3 :/ 2};});//skip 0 to initialize fpu successfully
    wdata[`RISCV_CSR_MSTATUS_FS] = fs;//FS
    wdata[`RISCV_CSR_MSTATUS_XS] = $urandom;//XS

  wdata[`RISCV_CSR_MSTATUS_MPRV] = mstatus_mprv;
    wdata[`RISCV_CSR_MSTATUS_MXR] = $urandom;
    wdata[`RISCV_CSR_MSTATUS_TVM] = $urandom;
    wdata[`RISCV_CSR_MSTATUS_TW] = $urandom;
    wdata[`RISCV_CSR_MSTATUS_TSR] = 0;  // tsr function is tested in separate test
    wdata[`RISCV_CSR_MSTATUS_SD] = $urandom;//SD
    mpp = wdata[`RISCV_CSR_MSTATUS_MPP];
    spp = wdata[`RISCV_CSR_MSTATUS_SPP];
    mprv = wdata[`RISCV_CSR_MSTATUS_MPRV];
    mxr = wdata[`RISCV_CSR_MSTATUS_MXR];
    tvm = wdata[`RISCV_CSR_MSTATUS_TVM];
    tw = wdata[`RISCV_CSR_MSTATUS_TW];
    tsr = wdata[`RISCV_CSR_MSTATUS_TSR];
  create_op_ld_gpr(tmp_gpr, wdata);
    create_op(OP_CSRRW, rd, tmp_gpr, 0, (`CSR_MSTATUS << 5), 1);
endtask

// NEED_CHANGE
task riscv_base_seq::create_final_op();
    // use self-loop instruction to end simulation
  if (gen_rvc_en == 1) begin
        create_op(OP_C_J, 0, 0, 0, 0, 1);
    end
    else begin
        create_op(OP_JAL, 0, 0, 0, 0, 1);
    end
endtask

// initialization for test running
task riscv_base_seq::test_init();
  // used for timeout check
  init_seconds = get_system_time();
  `uvm_info("debug", $psprintf("init_seconds = %0d", init_seconds), UVM_HIGH);

    // generate gpr_queue and fpr_queue and they could be used for GPR/FPR constraint
  gen_gpr_queue();
    gen_fpr_queue();
    
  // initialize CSR variables
  init_csr();

    // need to set each memory region, which may be used by others
  // Of all these region, m_code_region/m_data_region could be not accurate since inst jump/load/store is not constrainted by this
  init_mem_region();
    
    if (check_all_region_validity() == 1) begin
        `uvm_fatal("fatal", "mem region check failed");
    end

    // Optional configure pmp region
  //if (random_pmp_cfg == 0) begin
  //      init_pmp_cfg();
  //  end
  //  else begin
  //      init_random_pmp_cfg();
  //  end

  mtvec_mode = (($urandom%2)==0) ? 1 : 0;
  stvec_mode = (($urandom%2)==0) ? 1 : 0;

    m_curr_pc = init_start_pc;
  curr_mmode_isr_addr = m_init_mmode_trap_vector;
    curr_smode_isr_addr = m_init_smode_trap_vector;

    // initialize reserve gpr if anyone is used
  init_all_reserve_gpr();

    //config_pmp_region();
    //config_mcounteren();
    //config_mstatus();
    config_trap_vector();

    gen_init_gpr();
    init_gpr();
    if(fpu_inst_en ==1) init_fcsr();
    if(fpu_inst_en ==1) init_fpr();

    // setup trap handler
  if (nest_expt_en == 0) begin
    if (mtvec_mode == 1) begin
      init_mmode_vectored_isr();
    end
    else begin
      init_mmode_isr();
    end

    if (stvec_mode == 1) begin
      init_smode_vectored_isr();
    end
    else begin
            init_smode_isr();
    end
    end
    else begin
        init_mmode_isr_nest_expt();
    end

    //config_mtimecmp();
    //config_delegation();
    //config_interrupt_en();
    config_riscv_mode();

    // Indicate the end of boot code
  min_pc = m_curr_pc;

    // m_boot_pc is recording all boot instructions, will be used in other place
  for (bit[63:0] pc=init_start_pc; pc<min_pc; pc+=4) begin
        m_boot_pc[pc] = 1;
    end
endtask

// initialize m_mem[] with m_init_mem[]
function void riscv_base_seq::init_m_mem();
  bit [63:0] addr;

  m_mem.delete;

  if (m_init_mem.first(addr))
  do begin
    m_mem[addr] = m_init_mem[addr];
  end while (m_init_mem.next(addr));
endfunction: init_m_mem

//
// Branch control functions
//

// branch target address can't be in boot vector, trap vector, backdoor region
// return 0 if legal, return 1 if illegal
function int riscv_base_seq::check_target_addr(bit[63:0] addr);
    bit non_allow_br_target [*];
    bit [63:0] loop_pc;

    if (inst_arr.first(loop_pc))
    do begin
        if (inst_arr[loop_pc].inst_bin_code_size == 4) begin
            non_allow_br_target[loop_pc+2] = 1;
        end
    end while (inst_arr.next(loop_pc));

    if (m_boot_pc.exists(addr)) begin
        `uvm_info("debug", $psprintf("br target is in boot vector, addr = 0x%0x", addr), UVM_HIGH);
        return 1;
    end
    else if (m_tvec_pc.exists(addr)) begin
        `uvm_info("debug", $psprintf("br target is in trap vector, addr = 0x%0x", addr), UVM_HIGH);
        return 1;
    end
    else if (m_bkdr_data_region.is_addr_in_va_range(addr) == 1) begin
        `uvm_info("debug", $psprintf("br target is in backdoor memory region, addr = 0x%0x", addr), UVM_HIGH);
        return 1;
    end
    else if (non_allow_br_target.exists(addr)) begin
        `uvm_info("debug", $psprintf("br target is in non allow br target region, addr = 0x%0x", addr), UVM_HIGH);
        return 1;
    end
    else begin
        return 0;
    end
endfunction

// generate imm and target address for branch instruction, make sure branch target address is in valid range
// return 1 if gen fail, 0 if gen success
function bit riscv_base_seq::gen_br_target(bit only_forward_jump, ref riscv_inst_base_txn tr);
  int loop_cnt = 0;
  bit [63:0] base;
    bit [63:0] min_br_target;
    bit [63:0] max_br_target;

    max_br_target = tr.pc + br_range;
    if (tr.pc >= br_range) begin
        min_br_target = tr.pc - br_range;
    end
    else begin
        min_br_target = 0;
    end

  if (tr.inst_type == OP_JAL) begin
    do begin
      if (loop_cnt == 100) begin
        `uvm_info("debug", $psprintf("After looping 100 times, generated target_addr is still illegal, pc = 0x%0x, inst_type = 0x%0x", tr.pc, tr.inst_type), UVM_HIGH);
        return 1;
      end

      void'(tr.randomize(imm_64) with {
        imm_64[63:1] dist {[1:10]:/100, [11:'h7ffff]:/500, ['h7fff_ffff_fff8_0000:'h7fff_ffff_ffff_feff]:/300, ['h7fff_ffff_ffff_ff00:'h7fff_ffff_ffff_fff5]:/100, ['h7fff_ffff_ffff_fff6:'h7fff_ffff_ffff_fffe]:/10, 'h7fff_ffff_ffff_ffff:/1};

                if (pc[63:20] == min_pc[63:20]) {
            pc + signed'({imm_64[63:1], 1'b0}) >= min_pc;
                }

        if (br_range != 0) {
          pc + signed'({imm_64[63:1], 1'b0}) >= min_br_target;
          pc + signed'({imm_64[63:1], 1'b0}) <= max_br_target;
        }

                if (only_forward_jump == 1) {
            pc + signed'({imm_64[63:1], 1'b0}) > pc;
                }

                if (gen_rvc_en == 0) {
            (pc + signed'({imm_64[63:1], 1'b0})) % 4 == 0;
                }
                else {
            ((pc + signed'({imm_64[63:1], 1'b0})) % 4) dist {0:/1, 2:/1};
                }
        imm_64[20:1] != 0;
        imm_64[20:1] != 1;
      });
      tr.target = tr.pc + signed'({tr.imm_64[63:1], 1'b0});
      tr.imm = tr.imm_64[31:0];
      loop_cnt++;
    end while (check_target_addr(tr.target) == 1);
    `uvm_info("debug", $psprintf("generating a JAL, pc = 0x%0x, imm = 0x%0x, target_addr = 0x%0x, rd = %0d", tr.pc, tr.imm, tr.target, tr.rd), UVM_HIGH);
  end
  else if (tr.inst_type == OP_JALR) begin
    base = m_gpr[tr.rs1];

    do begin
      if (loop_cnt == 100) begin
        `uvm_info("debug", $psprintf("After looping 100 times, generated target_addr is still illegal, pc = 0x%0x, inst_type = 0x%0x", tr.pc, tr.inst_type), UVM_HIGH);
        return 1;
      end

      void'(tr.randomize(imm_64) with {
        imm_64 dist {0:/1, [1:10]:/2, [11:'h7ff]:/15, ['hffff_ffff_ffff_f800:'hffff_ffff_ffff_fff0]:/15, ['hffff_ffff_ffff_fff1:'hffff_ffff_ffff_fffe]:/2, 'hffff_ffff_ffff_ffff:/1};
                
                if (gen_rvc_en == 0) {
            (base + signed'(imm_64)) % 4 == 0;
                }
                else {
            ((base + signed'(imm_64)) % 4) dist {0:/1, 1:/1, 2:/1, 3:/1};
                }
        ((base + signed'(imm_64)) & 'hffff_ffff_ffff_fffe) != pc;
        ((base + signed'(imm_64)) & 'hffff_ffff_ffff_fffe) != pc + 2;
      });
      tr.target = (base + signed'(tr.imm_64)) & 'hffff_ffff_ffff_fffe;
      tr.imm = tr.imm_64[31:0];
      loop_cnt++;
    end while (check_target_addr(tr.target) == 1);
    `uvm_info("debug", $psprintf("generating a JALR, pc = 0x%0x, imm = 0x%0x, target_addr = 0x%0x, rs1 = %0d, m_gpr[rs1] = 0x%0x, rd = %0d", tr.pc, tr.imm, tr.target, tr.rs1, m_gpr[tr.rs1], tr.rd), UVM_HIGH);
  end
  else if (tr.inst_type == OP_BEQ || tr.inst_type == OP_BNE || tr.inst_type == OP_BLT || tr.inst_type == OP_BGE || tr.inst_type == OP_BLTU || tr.inst_type == OP_BGEU) begin
    do begin
      if (loop_cnt == 100) begin
        `uvm_info("debug", $psprintf("After looping 100 times, generated target_addr is still illegal, pc = 0x%0x, inst_type = 0x%0x", tr.pc, tr.inst_type), UVM_HIGH);
        return 1;
      end

      void'(tr.randomize(imm_64) with {
        imm_64[63:1] dist {[1:10]:/200, [11:'h7ff]:/500, ['h7fff_ffff_ffff_f800:'h7fff_ffff_ffff_feff]:/250, ['h7fff_ffff_ffff_ff00:'h7fff_ffff_ffff_fffe]:/50, 'h7fff_ffff_ffff_ffff:/1};
                
                if (pc[63:12] == min_pc[63:12]) {
            pc + signed'({imm_64[63:1], 1'b0}) >= min_pc;
                }

        if (br_range != 0) {
          pc + signed'({imm_64[63:1], 1'b0}) >= min_br_target;
          pc + signed'({imm_64[63:1], 1'b0}) <= max_br_target;
        }

                if (only_forward_jump == 1) {
          pc + signed'({imm_64[63:1], 1'b0}) > pc;
                }

                if (gen_rvc_en == 0) {
            (pc + signed'({imm_64[63:1], 1'b0})) % 4 == 0;
                }
                else {
            ((pc + signed'({imm_64[63:1], 1'b0})) % 4) dist {0:/1, 2:/1};
                }
        imm_64[12:1] != 0;
        imm_64[12:1] != 1;
      });
      tr.target = tr.pc + signed'({tr.imm_64[63:1], 1'b0});
      tr.imm = tr.imm_64[31:0];
      loop_cnt++;
    end while (check_target_addr(tr.target) == 1);
    `uvm_info("debug", $psprintf("generating a Bxx, pc = 0x%0x, inst_type = 0x%0x, imm = 0x%0x, target_addr = 0x%0x, rs1 = %0d, m_gpr[rs1] = 0x%0x, rs2 = %0d, m_gpr[rs2] = 0x%0x", tr.pc, tr.inst_type, tr.imm, tr.target, tr.rs1, m_gpr[tr.rs1], tr.rs2, m_gpr[tr.rs2]), UVM_HIGH);
  end
    else if (tr.inst_type == OP_C_J) begin
    do begin
      if (loop_cnt == 100) begin
        `uvm_info("debug", $psprintf("After looping 100 times, generated target_addr is still illegal, pc = 0x%0x, inst_type = 0x%0x", tr.pc, tr.inst_type), UVM_HIGH);
        return 1;
      end

      void'(tr.randomize(imm_64) with {
        imm_64[63:1] dist {[1:10]:/200, [11:'h3ff]:/500, ['h7fff_ffff_ffff_fc00:'h7fff_ffff_ffff_feff]:/250, ['h7fff_ffff_ffff_ff00:'h7fff_ffff_ffff_fffe]:/50, 'h7fff_ffff_ffff_ffff:/1};
                
                if (pc[63:11] == min_pc[63:11]) {
            pc + signed'({imm_64[63:1], 1'b0}) >= min_pc;
                }

        if (br_range != 0) {
          pc + signed'({imm_64[63:1], 1'b0}) >= min_br_target;
          pc + signed'({imm_64[63:1], 1'b0}) <= max_br_target;
        }

                if (only_forward_jump == 1) {
            pc + signed'({imm_64[63:1], 1'b0}) > pc;
                }

        ((pc + signed'({imm_64[63:1], 1'b0})) % 4) dist {0:/1, 2:/1};
        imm_64[11:1] != 0;
      });
      tr.target = tr.pc + signed'({tr.imm_64[63:1], 1'b0});
      tr.imm = tr.imm_64[31:0];
      loop_cnt++;
    end while (check_target_addr(tr.target) == 1);
    `uvm_info("debug", $psprintf("generating a C.J, pc = 0x%0x, imm[11:0] = 0x%0x, target_addr = 0x%0x", tr.pc, tr.imm[11:0], tr.target), UVM_HIGH);
  end
    else if (tr.inst_type == OP_C_JR || tr.inst_type == OP_C_JALR) begin
    tr.target = m_gpr[tr.rs1] & 'hffff_ffff_ffff_fffe;
        if (check_target_addr(tr.target) == 1 || tr.target == tr.pc) begin
      `uvm_info("debug", $psprintf("OP_C_JR/OP_C_JALR target is not illegal, pc = 0x%0x, inst_type = 0x%0x, target = 0x%0x", tr.pc, tr.inst_type, tr.target), UVM_HIGH);
      return 1;
        end
    `uvm_info("debug", $psprintf("generating a C.JR/C.JALR, pc = 0x%0x, rs1 = %0d, target_addr = 0x%0x", tr.pc, tr.rs1, tr.target), UVM_HIGH);
  end
    else if (tr.inst_type == OP_C_BEQZ || tr.inst_type == OP_C_BNEZ) begin
    do begin
      if (loop_cnt == 100) begin
        `uvm_info("debug", $psprintf("After looping 100 times, generated target_addr is still illegal, pc = 0x%0x, inst_type = 0x%0x", tr.pc, tr.inst_type), UVM_HIGH);
        return 1;
      end

      void'(tr.randomize(imm_64) with {
        imm_64[63:1] dist {[1:10]:/200, [11:'h7f]:/600, ['h7fff_ffff_ffff_ff80:'h7fff_ffff_ffff_ffcd]:/150, ['h7fff_ffff_ffff_ffce:'h7fff_ffff_ffff_fff5]:/50, ['h7fff_ffff_ffff_fff6:'h7fff_ffff_ffff_fffe]:/2, 'h7fff_ffff_ffff_ffff:/1};
                
        if (pc[63:8] == min_pc[63:8]) {
            pc + signed'({imm_64[63:1], 1'b0}) >= min_pc;
                }

        if (br_range != 0) {
          pc + signed'({imm_64[63:1], 1'b0}) >= min_br_target;
          pc + signed'({imm_64[63:1], 1'b0}) <= max_br_target;
        }

                if (only_forward_jump == 1) {
          pc + signed'({imm_64[63:1], 1'b0}) > pc;
                }

        ((pc + signed'({imm_64[63:1], 1'b0})) % 4) dist {0:/1, 2:/1};
        imm_64[8:1] != 0;
      });
      tr.target = tr.pc + signed'({tr.imm_64[63:1], 1'b0});
      tr.imm = tr.imm_64[31:0];
      loop_cnt++;
    end while (check_target_addr(tr.target) == 1);
    `uvm_info("debug", $psprintf("generating a C.BEQZ/C.BNEZ, pc = 0x%0x, inst_type = 0x%0x, imm[8:0] = 0x%0x, target_addr = 0x%0x, rs1 = %0d, m_gpr[rs1] = 0x%0x", tr.pc, tr.inst_type, tr.imm[8:0], tr.target, tr.rs1, m_gpr[tr.rs1]), UVM_HIGH);
  end
  else begin
    `uvm_fatal("impossible_condition", $psprintf("Should only be branch instruction in gen_br_target(), but got inst_type = 0x%0x, pc = 0x%0x", tr.inst_type, tr.pc));
  end

  return 0;
endfunction

// check pc range between branch target pc and current branch pc, put avaiable insert pc into insert_pc_queue
// put all loop pc into loop_pc_queue
// return 0 if success, return 1 if there is timeout error
function bit riscv_base_seq::gen_insert_pc_queue(riscv_inst_base_txn tr, bit[63:0] target_pc);
  bit [63:0] curr_pc;
  bit [63:0] next_pc;
    bit [31:0] inst_code;
  int inst_num = 0;
    int timeout_num = 10000;

  curr_pc = target_pc;

  // initialize insert_pc_queue and loop_pc_queue to be empty
  insert_pc_queue = {};
  loop_pc_queue = {};

  while (curr_pc != tr.pc) begin
    `uvm_info("my_debug", $psprintf("curr_pc = 0x%0x\n", curr_pc), UVM_DEBUG);
    if (!inst_arr.exists(curr_pc)) begin
            // there is possibility that max loop time is not enough and sequence is changed just inside this function(which means max_loop_time+1)
            // to not increase generation time, keep max loop time as a relatively small value
            // so for this case, just make insert_pc_queue empty and continue with flow
      //`uvm_fatal("impossible condition", $psprintf("Impossible condition happens, pc 0x%0x is not found in instruction array\n", curr_pc));
            `uvm_info("debug", $psprintf("sepcial scenario, pc 0x%0x is not in intruction array, make insert_pc_queue empty and continue flow", curr_pc), UVM_HIGH);
            insert_pc_queue = {};
            return 0;
    end
    else begin
      // store all loop pc
      loop_pc_queue.push_back(curr_pc);

      // store in insert_pc_queue unless it's key inst
      if (inst_arr[curr_pc].is_key_inst != 1 && check_fetch_fault_exception(curr_pc, get_fetch_size(inst_arr[curr_pc].inst_type)) == 0) begin
        insert_pc_queue.push_back(curr_pc);
        `uvm_info("my_debug", $psprintf("pushing pc 0x%0x to insert_pc_queue\n", curr_pc), UVM_DEBUG);
      end
    end
        
        for (int j=0; j<tr.pc_pa.size(); j++) begin
            inst_code = 0;
            for (int i=0; i<inst_arr[curr_pc].inst_bin_code_size; i++) begin
                inst_code += m_mem[inst_arr[curr_pc].pc_pa[j][64*i+:64]] << 8*i;
            end
            inst_arr[curr_pc].inst_decode(inst_code);
        end

    next_pc = calculate_op(inst_arr[curr_pc].inst_type, curr_pc, inst_arr[curr_pc].rd, inst_arr[curr_pc].rs1, inst_arr[curr_pc].rs2, inst_arr[curr_pc].imm);

    curr_pc = next_pc;

    inst_num++;
        if (inst_num > timeout_num) begin
            `uvm_info("debug", $psprintf("After %0d instrution, still not finish loop, timeout and exit", inst_num), UVM_HIGH);
            return 1;
        end
  end

  return 0;
endfunction

// generate insert_pc to insert forward branch
// And check whether insert JAL/C_J is able to jump out of loop. If not, return 0. Otherwise, return 1
function bit riscv_base_seq::gen_insert_pc(riscv_inst_base_txn tr);
  int valid_insert_pc_idx[$];
  int idx;

  for (int i=0; i<insert_pc_queue.size(); i++) begin
        if (inst_arr[insert_pc_queue[i]].inst_bin_code_size == 2) begin
        if (insert_pc_queue[i] + 'h7fe > tr.pc) begin
          valid_insert_pc_idx.push_back(i);
        end
        end
        else begin
        if (insert_pc_queue[i] + 'hffffe > tr.pc) begin
          valid_insert_pc_idx.push_back(i);
        end
        end
  end

  if (valid_insert_pc_idx.size() != 0) begin
    idx = $urandom_range(0, valid_insert_pc_idx.size()-1);
    insert_pc_idx = valid_insert_pc_idx[idx];
    insert_pc = insert_pc_queue[insert_pc_idx];
    `uvm_info("debug", $psprintf("insert_pc_idx = %0d, insert_pc = 0x%0x, size = %0d\n", insert_pc_idx, insert_pc, insert_pc_queue.size()), UVM_HIGH);
    return 1;
  end
  else begin
    insert_pc_idx = $urandom_range(0, insert_pc_queue.size()-1);
    insert_pc = insert_pc_queue[insert_pc_idx];
    `uvm_info("debug", $psprintf("insert_pc_idx = %0d, insert_pc = 0x%0x, size = %0d\n", insert_pc_idx, insert_pc, insert_pc_queue.size()), UVM_HIGH);
    return 0;
  end
endfunction

// insert JAL as forward branch to jump out of loop
// return 1 if needing re-randomize, return 0 otherwise
function bit riscv_base_seq::insert_jal(riscv_inst_base_txn tr, bit can_jump_off_loop);
  int loop_cnt = 0;
  riscv_inst_base_txn temp_txn;
  bit [63:0] insert_jal_min_pc;

  temp_txn = riscv_inst_base_txn::type_id::create("temp_txn",,get_full_name());
  temp_txn.pc = inst_arr[insert_pc].pc;
  temp_txn.inst_bin_code_size = inst_arr[insert_pc].inst_bin_code_size;

  if (can_jump_off_loop) begin
    insert_jal_min_pc = tr.pc;
  end
  else begin
    insert_jal_min_pc = temp_txn.pc;
  end

  // insert OP_JAL or OP_C_J
    do begin
    if (loop_cnt == 10) begin
      return 1;
    end

    void'(temp_txn.randomize(imm_64) with {
            if (inst_arr[insert_pc].inst_bin_code_size == 2) {
        imm_64[63:1] dist {[1:10]:/2, [11:'h3ff]:/5, ['h7fff_ffff_ffff_fc00:'h7fff_ffff_ffff_feff]:/5, ['h7fff_ffff_ffff_ff00:'h7fff_ffff_ffff_fffe]:/2, 'h7fff_ffff_ffff_ffff:/1};
            }
            else {
                imm_64[63:1] dist {[1:5]:/2, [6:'h7ffff]:/5, ['h7fff_ffff_fff8_0000:'h7fff_ffff_ffff_fff9]:/5, ['h7fff_ffff_ffff_fffa:'h7fff_ffff_ffff_fffe]:/2, 'h7fff_ffff_ffff_ffff:/1};
            }

      pc + signed'({imm_64[63:1], 1'b0}) > insert_jal_min_pc;
      
            if (br_range != 0) {
        pc + signed'({imm_64[63:1], 1'b0}) <= tr.pc + br_range;
      }
      
            if (can_jump_off_loop == 0) {
        !((pc + signed'({imm_64[63:1], 1'b0})) inside {loop_pc_queue});
      }
      
            if (gen_rvc_en == 0) {
                (pc + signed'({imm_64[63:1], 1'b0})) % 4 == 0;
            }
            else {
          ((pc + signed'({imm_64[63:1], 1'b0})) % 4) dist {0:/1, 2:/1};
            }
    });
    loop_cnt++;
  end while (check_target_addr(temp_txn.pc + signed'({temp_txn.imm_64[63:1], 1'b0})) == 1);

  inst_arr[insert_pc].inst_type = (inst_arr[insert_pc].inst_bin_code_size == 2) ? OP_C_J : OP_JAL;
  inst_arr[insert_pc].is_key_inst = 1;
  inst_arr[insert_pc].imm_64 = temp_txn.imm_64;
  inst_arr[insert_pc].imm = inst_arr[insert_pc].imm_64[31:0];
  `uvm_info("debug", $psprintf("Inserting a forward branch JAL/C_J to avoid dead lock, inst_type = 0x%0x, pc = 0x%0x, imm = 0x%0x, target_addr = 0x%0x, rd = 0x%0x\n", inst_arr[insert_pc].inst_type, inst_arr[insert_pc].pc, inst_arr[insert_pc].imm, inst_arr[insert_pc].pc + signed'({inst_arr[insert_pc].imm_64[63:1], 1'b0}), inst_arr[insert_pc].rd), UVM_HIGH);

  return 0;
endfunction


// Try to fix branch dead loop by modifying some previous generated instructions
function riscv_base_seq::fix_dead_loop_result_e riscv_base_seq::fix_br_dead_loop(ref riscv_inst_base_txn tr, bit[63:0] target_addr);
  bit result;
  bit can_jump_off_loop;

  `uvm_info("debug", $psprintf("Entering fix_br_dead_loop, pc = 0x%0x, target = 0x%0x, inst_type = 0x%0x, rs1 = %0d, rs2 = %0d, rd = %0d\n", tr.pc, target_addr, tr.inst_type, tr.rs1, tr.rs2, tr.rd), UVM_HIGH);

  // No place to insert key inst
  // This can't be fixed outside, change to be a ALU inst
  if (insert_pc_queue.size() == 0) begin
    `uvm_info("debug", $psprintf("no place to insert key inst for pc 0x%0x\n", tr.pc), UVM_HIGH);
    if (tr.is_key_inst == 1) begin
      `uvm_info("debug", $psprintf("curr_pc is key_inst and can't be changed, pc = 0x%0x\n", tr.pc), UVM_HIGH);
      return FIX_FAIL;
    end
    else begin
      if (tr.inst_bin_code_size == 2) begin
          tr.inst_type = inst_type_e'($urandom_range('h132, 'h137));
      end
      else begin
          tr.inst_type = inst_type_e'($urandom_range('h0, 'h1d));
      end
      `uvm_info("debug", $psprintf("changing curr inst_type to 0x%0x for pc 0x%0x\n", tr.inst_type, tr.pc), UVM_HIGH);
      return FIX_MODIFY;
    end
  end

  // generate insert_pc to insert forward branch
  can_jump_off_loop = gen_insert_pc(tr);

  result = insert_jal(tr, can_jump_off_loop);
  if (result == 1) begin
    `uvm_info("debug", $psprintf("insert_jal fix fail for pc 0x%0x\n", tr.pc), UVM_HIGH);
    return FIX_FAIL;
  end
  else if (can_jump_off_loop == 0) begin
    `uvm_info("debug", $psprintf("insert_jal fix retry due to can_jump_off_loop==0 for pc 0x%0x\n", tr.pc), UVM_HIGH);
    return FIX_RETRY;
  end
  else begin
    `uvm_info("debug", $psprintf("insert_jal fix done for pc 0x%0x\n", tr.pc), UVM_HIGH);
    return FIX_DONE;
  end
endfunction

function void riscv_base_seq::print_gpr();
  for (int i=0; i<32; i++) begin
    `uvm_info("debug", $psprintf("m_gpr[%0d] = 0x%0x", i, m_gpr[i]), UVM_HIGH);
  end
endfunction

// Try to generate valid sequence
// return 0 if success, return 1 if failed
function bit riscv_base_seq::gen_valid_sequence(int inst_num, ref bit[63:0] last_pc);
    bit [63:0] curr_pc;
    bit [63:0] next_pc;
    bit [63:0] jalr_pc;
    bit [63:0] loop_pc;
    bit [63:0] exit_pc;
    bit [63:0] curr_pc_pa_0;
    bit [63:0] curr_pc_pa_1;
    bit [63:0] curr_pc_pa_2;
    bit [63:0] curr_pc_pa_3;
    bit [255:0] next_pc_pa_whole;
    bit [4:0] jalr_rs1;
    bit [63:0] pa;
    bit [4:0] tmp_gpr1;
    bit [4:0] tmp_gpr2;
    bit [4:0] tmp_gpr3;
    bit [63:0] original_m_curr_pc;
    bit [31:0] jalr_imm;
    bit found_inst_code_change;
    bit next_pc_valid;
  int back_br_arr [*];
  bit [63:0] target;
  riscv_inst_base_txn tmp_txn;
  riscv_inst_base_txn txn;
  fix_dead_loop_result_e fix_result;
  int retry_times = 0;
    bit [31:0] inst_code;
    bit [31:0] last_inst_code;
    int jalr_idx;
    bit loop_retry = 0;
    bit pc_arr [*];
    bit re_loop;
    bit re_randomize;
    bit [63:0] lsu_va;
    bit [63:0] lsu_pa;
    bit [63:0] loop_lsu_pc;
    int lsu_st_bytes;
    bit [63:0] target_pc[$];
    bit [255:0] curr_pc_pa;
    bit fetch_exception;
  bit result;
  bit gen_inst_32_en;
    int valid_next_pc_bytes;
    int invalid_pa_num;
  bit gen_fail;

    curr_pc = init_start_pc;
  for (int i=0; i<32; i++) begin
    m_gpr[i] = 0;
  end
  init_m_mem();
  init_csr();

    while (pc_arr.num() < inst_num) begin
    // check TB timeout
    if (pc_arr.num() % 1000 == 0) begin
      curr_seconds = get_system_time();
      if ((curr_seconds - init_seconds) > timeout_seconds) begin
        `uvm_warning("warning", $psprintf("TB generation timeout, exit with boot sequence, curr_seconds = %0d, init_seconds = %0d, delta_seconds = %0d", curr_seconds, init_seconds, curr_seconds-init_seconds));

                // reset all control variables
                if (inst_arr.first(loop_pc)) 
        do begin
                    if (!m_boot_pc.exists(loop_pc) && !m_tvec_pc.exists(loop_pc)) begin
            inst_arr.delete(loop_pc);
          end
        end while (inst_arr.next(loop_pc));

                curr_pc = min_pc;
                break;
      end
    end


        invalid_pa_num = 0;
        for (int j=0; j<inst_arr[curr_pc].pc_pa.size(); j++) begin
            inst_code = 0;
            if (inst_arr[curr_pc].pc_pa[j] != 'hdeadbeef_deadbeef_deadbeef_deadbeef_deadbeef_deadbeef_deadbeef_deadbeef) begin
                for (int i=0; i<inst_arr[curr_pc].inst_bin_code_size; i++) begin
                    inst_code += m_mem[inst_arr[curr_pc].pc_pa[j][64*i+:64]] << 8*i;
                end

                if (j > invalid_pa_num && inst_code != last_inst_code) begin
                    `uvm_fatal("fatal", $psprintf("found different inst_code for pc = 0x%0x, last_pc_pa = 0x%0x, curr_pc_pa = 0x%0x, last_inst_code = 0x%0x, curr_inst_code = 0x%0x, j = %0d", curr_pc, inst_arr[curr_pc].pc_pa[j-1], inst_arr[curr_pc].pc_pa[j], last_inst_code, inst_code, j));
                end

                last_inst_code = inst_code;
            end
            else begin
                invalid_pa_num++;
            end
        end

        inst_arr[curr_pc].inst_decode(inst_code);

        if (gen_rvc_en == 0 && inst_arr[curr_pc].is_c_extension_inst(inst_code) == 1 && inst_arr[curr_pc].is_dummy_inst != 1) begin
            `uvm_info("debug", $psprintf("Found a c-extension instruction which is not supposed to be generated with gen_rvc_en=0, re-randomize, pc = 0x%0x, inst_code = 0x%0x", curr_pc, inst_code), UVM_HIGH);
            return 1;
        end

        // check whether there is new pc_pa. If so, need to store instruction code again to new address
    if (inst_arr[curr_pc].is_dummy_inst != 1) begin
      curr_pc_pa = 0;
            invalid_pa_num = 0;
            for (int i=0; i<inst_arr[curr_pc].inst_bin_code_size; i++) begin
        curr_pc_pa[64*i+:64] = get_pa(inst_arr[curr_pc].pc+i, 1, 0);
                if (curr_pc_pa[64*i+:64] == 'hdeadbeef_deadbeef) begin
                    invalid_pa_num = 1;
                end
      end
          if (inst_arr[curr_pc].is_in_pc_pa_queue(curr_pc_pa) == 0 && invalid_pa_num == 0) begin
              inst_arr[curr_pc].pc_pa.push_back(curr_pc_pa);
              `uvm_info("debug", $psprintf("found new pc_pa, curr_pc = 0x%0x, new_pc_pa = 0x%0x", curr_pc, curr_pc_pa), UVM_HIGH);

          curr_pc_pa_0 = curr_pc_pa[63:0];
          curr_pc_pa_1 = curr_pc_pa[127:64];
                if (inst_arr[curr_pc].inst_bin_code_size > 2) begin
            curr_pc_pa_2 = curr_pc_pa[191:128];
            curr_pc_pa_3 = curr_pc_pa[255:192];
                end
                else begin
            curr_pc_pa_2 = curr_pc_pa_0;
            curr_pc_pa_3 = curr_pc_pa_0;
                end

                // check new pc_pa will not override any existing pc's pa
                if (inst_arr.first(loop_pc))
                do begin
                    if (loop_pc != curr_pc) begin
                        for (int i=0; i<inst_arr[loop_pc].pc_pa.size(); i++) begin
                  for (int j=0; j<inst_arr[loop_pc].inst_bin_code_size; j++) begin
                    if (curr_pc_pa_0 == inst_arr[loop_pc].pc_pa[i][64*j+:64] || 
                      curr_pc_pa_1 == inst_arr[loop_pc].pc_pa[i][64*j+:64] || 
                      curr_pc_pa_2 == inst_arr[loop_pc].pc_pa[i][64*j+:64] || 
                      curr_pc_pa_3 == inst_arr[loop_pc].pc_pa[i][64*j+:64]) begin
                                  `uvm_info("debug", $psprintf("found override existing pc pa, curr_pc = 0x%0x, curr_pc_pa_0 = 0x%0x, curr_pc_pa_1 = 0x%0x, curr_pc_pa_2 = 0x%0x, curr_pc_pa_3 = 0x%0x, loop_pc = 0x%0x", curr_pc, curr_pc_pa_0, curr_pc_pa_1, curr_pc_pa_2, curr_pc_pa_3, loop_pc), UVM_HIGH);
                                  return 1;
                              end
                  end
                        end
                    end
                end while (inst_arr.next(loop_pc));

              store_inst_code(inst_arr[curr_pc]);
          end
    end
    else begin
            // check if dummy inst become valid inst due to memory translation mode change
            if (check_mem_trans_access_violation(curr_pc, 2, 1, 0) == 0) begin
                if (check_mem_trans_access_violation(curr_pc, 4, 1, 0) == 0) begin
                    inst_arr[curr_pc].inst_bin_code_size = 4;
                end
                else begin
                    inst_arr[curr_pc].inst_bin_code_size = 2;
                end

                inst_code = 0;
                curr_pc_pa = 0;
                for (int i=0; i<inst_arr[curr_pc].inst_bin_code_size; i++) begin
            curr_pc_pa[64*i+:64] = get_pa(curr_pc+i, 1, 0);
                    inst_code += m_mem[curr_pc_pa[64*i+:64]] << 8*i;
          end

                // replace original pc_pa which is deadbeef
                inst_arr[curr_pc].pc_pa[0] = curr_pc_pa;

                // decode to get new op info for original dummy inst
                inst_arr[curr_pc].inst_decode(inst_code);
            end
            else begin
          curr_pc_pa = 'hdeadbeef_deadbeef_deadbeef_deadbeef_deadbeef_deadbeef_deadbeef_deadbeef;
            end
    end

        // for csr instruction not in boot or trap vector, re-randomize since we don't support calculating all CSRs
        // these non-0-rd inst are caused by later store modifying inst code
        if (!m_tvec_pc.exists(curr_pc) && !m_boot_pc.exists(curr_pc)) begin
            if ((inst_arr[curr_pc].inst_type >= OP_CSRRW && inst_arr[curr_pc].inst_type <= OP_CSRRCI) &&
                (inst_arr[curr_pc].rd != 0) &&
                 inst_arr[curr_pc].csr != `CSR_MTIMECMP &&
                 inst_arr[curr_pc].csr != `CSR_MIE &&
                 inst_arr[curr_pc].csr != `CSR_MSCRATCH &&
                 inst_arr[curr_pc].csr != `CSR_SSCRATCH &&
                 inst_arr[curr_pc].csr != `CSR_MEDELEG &&
                 inst_arr[curr_pc].csr != `CSR_MIDELEG &&
                 inst_arr[curr_pc].csr != `CSR_MCOUNTEREN &&
                 inst_arr[curr_pc].csr != `CSR_SCOUNTEREN
                ) begin
                `uvm_info("debug", $psprintf("found non-boot/trap csr inst rd is not 0, re-randomize, curr_pc = 0x%0x, inst_type = 0x%0x, rd = %0d", curr_pc, inst_arr[curr_pc].inst_type, inst_arr[curr_pc].rd), UVM_HIGH);
                return 1;
            end
        end

    next_pc = calculate_op(inst_arr[curr_pc].inst_type, curr_pc, inst_arr[curr_pc].rd, inst_arr[curr_pc].rs1, inst_arr[curr_pc].rs2, inst_arr[curr_pc].imm);

        if (next_pc == curr_pc) begin
            `uvm_info("debug", $psprintf("Found a self-loop inst, re-randomize, pc = 0x%0x, inst_type = 0x%0x, rd = %0d, rs1 = %0d, rs2 = %0d, imm = 0x%0x", curr_pc, inst_arr[curr_pc].inst_type, inst_arr[curr_pc].rd, inst_arr[curr_pc].rs1, inst_arr[curr_pc].rs2, inst_arr[curr_pc].imm), UVM_HIGH);
            return 1;
        end

        if (!m_tvec_pc.exists(curr_pc) && !m_boot_pc.exists(curr_pc) && rsvd_gpr_arr.exists(inst_arr[curr_pc].rd) && inst_arr[curr_pc].is_rd_valid == 1 && next_pc != m_curr_mmode_trap_vector && next_pc != m_curr_smode_trap_vector && (inst_arr[curr_pc].inst_type inside {OP_FEQ_S, OP_FLT_S, OP_FLE_S, OP_FCLASS_S, OP_FMV_X_S, OP_FCVT_W_S, OP_FCVT_WU_S, OP_FCVT_L_S, OP_FCVT_LU_S} || !(inst_arr[curr_pc].inst_type inside {['h70:'h8d]})) ) begin
            `uvm_info("debug", $psprintf("rd is in rsvd_gpr_arr, re-randomize, curr_pc = 0x%0x, rd = %0d", curr_pc, inst_arr[curr_pc].rd), UVM_HIGH);
            return 1;
        end

        if (!m_tvec_pc.exists(curr_pc)) begin
            pc_arr[curr_pc] = 1;
        end

        //if (!m_boot_pc.exists(curr_pc)) begin
            `uvm_info("debug", $psprintf("in gen_valid_sequence(), pc = 0x%0x, pc_pa = 0x%0x, inst_type = 0x%0x, next_pc = 0x%0x, rd = %0d, rs1 = %0d, rs2 = %0d, imm = 0x%0x, m_gpr[rs1] = 0x%0x, m_gpr[rd] = 0x%0x, is_change_store_inst = %0d, inst_code = 0x%0x, cause = %0d, pc_num = %0d", curr_pc, curr_pc_pa[63:0], inst_arr[curr_pc].inst_type, next_pc, inst_arr[curr_pc].rd, inst_arr[curr_pc].rs1, inst_arr[curr_pc].rs2, inst_arr[curr_pc].imm, m_gpr[inst_arr[curr_pc].rs1], m_gpr[inst_arr[curr_pc].rd], inst_arr[curr_pc].is_change_store_inst, inst_code, cause, pc_arr.num()), UVM_DEBUG);
      //print_gpr();
        //end

        // record backward branch times
        if (!inst_arr.exists(next_pc)) begin
            next_pc_valid = 0;
        end
        else begin
            next_pc_valid = ~inst_arr[next_pc].is_isr_inst;
        end

    if (next_pc < curr_pc && inst_arr[curr_pc].is_isr_inst == 0 && next_pc_valid == 1) begin
      if (back_br_arr.exists(curr_pc)) begin
        back_br_arr[curr_pc]++;
        // assume this is a dead loop
        if (back_br_arr[curr_pc] > max_loop_times) begin
          target = next_pc;
          result = gen_insert_pc_queue(inst_arr[curr_pc], target);
          if (result == 1) begin
                        `uvm_info("debug", $psprintf("re-randomize due to gen_insert_pc_queue timeout"), UVM_HIGH);
                        return 1;
                    end
          tmp_txn = riscv_inst_base_txn::type_id::create("tmp_txn",,get_full_name());
          tmp_txn.copy(inst_arr[curr_pc]);
          fix_result = fix_br_dead_loop(tmp_txn, target);
          inst_arr[curr_pc].inst_type = tmp_txn.inst_type;

                    store_inst_code(inst_arr[curr_pc]);

                    if (fix_result != FIX_FAIL && fix_result != FIX_MODIFY) begin
                        store_inst_code(inst_arr[insert_pc]);
                    end

          if (fix_result == FIX_FAIL) begin
            `uvm_info("debug", $psprintf("FIX_FAIL, can't fix dead loop for pc 0x%0x\n", curr_pc), UVM_HIGH);
            return 1;
          end
          else if (fix_result == FIX_RETRY) begin
            retry_times++;
            `uvm_info("debug", $psprintf("FIX_RETRY, pc = 0x%0x, retry_times = %0d\n", curr_pc, retry_times), UVM_HIGH);
            if (retry_times > 1000) begin
              `uvm_info("debug", $psprintf("FIX_FAIL, retry too many times and still can't fix, last_retry_pc = 0x%0x\n", curr_pc), UVM_HIGH);
              return 1;
            end
          end

          // re-initialize all variable and retry full sequence in inst_arr[]
          curr_pc = init_start_pc;
          back_br_arr.delete;
                    pc_arr.delete;
                    accessed_lsu_pa_arr.delete;
          for (int i=0; i<32; i++) begin
            m_gpr[i] = 0;
          end
                    loop_retry = 0;
          init_m_mem();
          init_csr();
          continue;
        end
      end
      else begin
        back_br_arr[curr_pc] = 1;
      end
    end

        if ((inst_arr[curr_pc].inst_type == OP_SB || inst_arr[curr_pc].inst_type == OP_SH || inst_arr[curr_pc].inst_type == OP_SW || inst_arr[curr_pc].inst_type == OP_FSW || inst_arr[curr_pc].inst_type == OP_SD || inst_arr[curr_pc].inst_type == OP_C_SW || inst_arr[curr_pc].inst_type == OP_C_SWSP || inst_arr[curr_pc].inst_type == OP_C_SD || inst_arr[curr_pc].inst_type == OP_C_SDSP) && next_pc != m_curr_mmode_trap_vector && next_pc != m_curr_smode_trap_vector) begin
            lsu_va = get_lsu_va(inst_arr[curr_pc]);
            lsu_st_bytes = get_st_bytes(inst_arr[curr_pc].inst_type);
            target_pc = {};
            if (is_overlap_with_exist_pc(lsu_va, lsu_st_bytes, 0, target_pc) == 1) begin
                fetch_exception = 1;
                for (int i=0; i<target_pc.size(); i++) begin
                    if (check_mem_trans_access_violation(target_pc[i], get_fetch_size(inst_arr[target_pc[i]].inst_type), 1, 0) == 0) begin
                        fetch_exception = 0;
                    end
                end

                if (fetch_exception == 0) begin
                    if (inst_arr[curr_pc].inst_type == OP_SB) begin
                        inst_arr[curr_pc].inst_type = $urandom ? OP_LB : OP_LBU;
                    end
                    else if (inst_arr[curr_pc].inst_type == OP_SH) begin
                        inst_arr[curr_pc].inst_type = $urandom ? OP_LH : OP_LHU;
                    end
                    else if (inst_arr[curr_pc].inst_type == OP_SW) begin
                        inst_arr[curr_pc].inst_type = $urandom ? OP_LW : OP_LWU;
                    end
                    else if (inst_arr[curr_pc].inst_type == OP_FSW) begin
                        inst_arr[curr_pc].inst_type = OP_FLW;
                    end
                    else if (inst_arr[curr_pc].inst_type == OP_SD) begin
                        inst_arr[curr_pc].inst_type = OP_LD;
                    end
                    else if (inst_arr[curr_pc].inst_type == OP_C_SW) begin
                        inst_arr[curr_pc].inst_type = OP_C_LW;
                    end
                    else if (inst_arr[curr_pc].inst_type == OP_C_SWSP) begin
                        inst_arr[curr_pc].inst_type = OP_C_LWSP;
                    end
                    else if (inst_arr[curr_pc].inst_type == OP_C_SD) begin
                        inst_arr[curr_pc].inst_type = OP_C_LD;
                    end
                    else if (inst_arr[curr_pc].inst_type == OP_C_SDSP) begin
                        inst_arr[curr_pc].inst_type = OP_C_LDSP;
                    end
                    else begin
                        `uvm_fatal("fatal", $psprintf("unexpected inst_type 0x%0x", inst_arr[curr_pc].inst_type));
                    end

                    inst_arr[curr_pc].rd = 0;
                    inst_arr[curr_pc].is_change_store_inst = 1;

                    store_inst_code(inst_arr[curr_pc]);

                    `uvm_info("debug", $psprintf("change store code address inst (pc = 0x%0x) to load", curr_pc), UVM_HIGH);
                    for (int i=0; i<target_pc.size(); i++) begin
                        `uvm_info("debug", $psprintf("target_pc[%0d] = 0x%0x", i, target_pc[i]), UVM_HIGH);
                    end

                    // reloop
                    curr_pc = init_start_pc;
              back_br_arr.delete;
                    pc_arr.delete;
                    accessed_lsu_pa_arr.delete;
              for (int i=0; i<32; i++) begin
                m_gpr[i] = 0;
              end
              loop_retry = 0;
              init_m_mem();
              init_csr();
              continue;
                end
            end
        end

        // when fbif bus fault is enabled, avoid sending store with fault address
        // because cmod/vmod can't sync for cache hit/miss, we need to make sure load fault address will always miss for cache
    // NEED_CHANGE, may not need if no such issue
        if ((inst_arr[curr_pc].inst_type == OP_SB || inst_arr[curr_pc].inst_type == OP_SH || inst_arr[curr_pc].inst_type == OP_SW || inst_arr[curr_pc].inst_type == OP_FSW || inst_arr[curr_pc].inst_type == OP_SD || inst_arr[curr_pc].inst_type == OP_C_SW || inst_arr[curr_pc].inst_type == OP_C_SWSP || inst_arr[curr_pc].inst_type == OP_C_SD || inst_arr[curr_pc].inst_type == OP_C_SDSP) && next_pc != m_curr_mmode_trap_vector && next_pc != m_curr_smode_trap_vector) begin
            lsu_pa = get_lsu_pa(inst_arr[curr_pc]);
            lsu_pa = lsu_pa & 'hffff_ffff_ffff_ffc0;

            // TODO: discuss with Neo Fang.
            //if (riscv_mem::fbif_err.exists(lsu_pa)) begin
            //    if (inst_arr[curr_pc].inst_type == OP_SB) begin
            //        inst_arr[curr_pc].inst_type = $urandom ? OP_LB : OP_LBU;
            //    end
            //    else if (inst_arr[curr_pc].inst_type == OP_SH) begin
            //        inst_arr[curr_pc].inst_type = $urandom ? OP_LH : OP_LHU;
            //    end
            //    else if (inst_arr[curr_pc].inst_type == OP_SW) begin
            //        inst_arr[curr_pc].inst_type = $urandom ? OP_LW : OP_LWU;
            //    end
            //    else if (inst_arr[curr_pc].inst_type == OP_FSW) begin
            //        inst_arr[curr_pc].inst_type = OP_FLW;
            //    end
            //    else if (inst_arr[curr_pc].inst_type == OP_SD) begin
            //        inst_arr[curr_pc].inst_type = OP_LD;
            //    end
            //    else if (inst_arr[curr_pc].inst_type == OP_C_SW) begin
            //        inst_arr[curr_pc].inst_type = OP_C_LW;
            //    end
            //    else if (inst_arr[curr_pc].inst_type == OP_C_SWSP) begin
            //        inst_arr[curr_pc].inst_type = OP_C_LWSP;
            //    end
            //    else if (inst_arr[curr_pc].inst_type == OP_C_SD) begin
            //        inst_arr[curr_pc].inst_type = OP_C_LD;
            //    end
            //    else if (inst_arr[curr_pc].inst_type == OP_C_SDSP) begin
            //        inst_arr[curr_pc].inst_type = OP_C_LDSP;
            //    end
            //    else begin
            //        `uvm_fatal("fatal", $psprintf("unexpected inst_type 0x%0x", inst_arr[curr_pc].inst_type));
            //    end
            //
            //    store_inst_code(inst_arr[curr_pc]);
            //
            //    `uvm_info("debug", $psprintf("change store code address inst (pc = 0x%0x) to load, because it's storing fbif fault address, st_pa = 0x%0x", curr_pc, lsu_pa), UVM_HIGH);
            //
            //    // re loop
            //    curr_pc = init_start_pc;
            //    back_br_arr.delete;
            //    pc_arr.delete;
            //    accessed_lsu_pa_arr.delete;
            //    for (int i=0; i<32; i++) begin
            //      m_gpr[i] = 0;
            //    end
            //    loop_retry = 0;
            //    init_m_mem();
            //    init_csr();
            //    continue;
            //end
            //
        end

        // change rd of fpu inst which will change gpr
        if (inst_arr[curr_pc].inst_type inside {OP_FEQ_S, OP_FLT_S, OP_FLE_S, OP_FCLASS_S, OP_FMV_X_S, OP_FCVT_W_S, OP_FCVT_WU_S, OP_FCVT_L_S, OP_FCVT_LU_S} && inst_arr[curr_pc].rd !=0 && (curr_pc +4) == next_pc ) begin
                `uvm_info("debug", $psprintf("found fpu inst with rd: %0d", inst_arr[curr_pc].rd), UVM_HIGH);
                //set rd to 0
                inst_arr[curr_pc].rd = 0;
                store_inst_code(inst_arr[curr_pc]);
        end

        if ((is_in_boot_pc_range(next_pc) && !is_in_boot_pc_range(curr_pc)) ||
            (is_in_tvec_pc_range(next_pc) && !is_in_tvec_pc_range(curr_pc) && next_pc != m_curr_mmode_trap_vector && next_pc != m_curr_smode_trap_vector) ||
            (m_bkdr_data_region.is_addr_in_va_range(next_pc) == 1) ||
            (m_stack_region.is_addr_in_va_range(next_pc) == 1)) begin
            if (inst_arr[curr_pc].inst_type == OP_JALR || inst_arr[curr_pc].inst_type == OP_C_JR || inst_arr[curr_pc].inst_type == OP_C_JALR) begin
                `uvm_info("debug", $psprintf("JALR target is in reserve region, re-randomize"), UVM_HIGH);

                jalr_rs1 = inst_arr[curr_pc].rs1;
                void'(inst_arr[curr_pc].randomize(rs1) with {
                    rs1 inside {gpr_queue};
                    rs1 != jalr_rs1;
                    if (inst_type == OP_C_JR || inst_type == OP_C_JALR) {
                        rs1 >= 8;
                        rs1 <= 15;
                    }

                });
                
                store_inst_code(inst_arr[curr_pc]);

                curr_pc = init_start_pc;
        back_br_arr.delete;
                pc_arr.delete;
                accessed_lsu_pa_arr.delete;
              for (int i=0; i<32; i++) begin
                m_gpr[i] = 0;
              end
                loop_retry = 0;
              init_m_mem();
                init_csr();
                continue;
            end
            else begin
                if (m_boot_pc.exists(curr_pc)) begin
                    `uvm_fatal("fatal", $psprintf("non-JALR next_pc is in reserve region, but curr_pc is in boot vector, curr_pc = 0x%0x", curr_pc));
                end
                else begin
                    `uvm_info("debug", $psprintf("non-JALR next_pc is in reserve region, curr_pc = 0x%0x, exit_pc = 0x%0x", curr_pc, exit_pc), UVM_HIGH);
                    re_loop = 0;
                    re_randomize = 0;
                    if (curr_pc == exit_pc) begin
                        if (m_tvec_pc.exists(curr_pc) || check_mem_trans_access_violation(curr_pc, get_fetch_size(inst_arr[curr_pc].inst_type), 1, 0) == 1) begin
                            `uvm_info("debug", $psprintf("curr_pc is in trap/boot vector or has memory access violation"), UVM_HIGH);
                            re_loop = 1;
                            re_randomize = 1;
                        end
                        else begin
                            next_pc_pa_whole = 0;
                            for (int i=0; i<inst_arr[curr_pc].inst_bin_code_size; i++) begin
                next_pc_pa_whole[64*i+:64] = va2pa(curr_pc+i, 1);
              end
                            if (is_pc_accessed_by_lsu(next_pc_pa_whole, inst_arr[curr_pc].inst_bin_code_size) == 1) begin
                                `uvm_info("debug", $psprintf("curr_pc has been accessed before by LSU inst, pc_pa = 0x%0x", next_pc_pa_whole), UVM_HIGH);
                                re_loop = 1;
                                re_randomize = 1;
                            end
                            else if (loop_retry == 1) begin
                                `uvm_info("debug", $psprintf("loop_retry = 1, need to re-loop again"), UVM_HIGH);
                                re_loop = 1;
                            end
                            else begin
                                `uvm_info("debug", $psprintf("end total sequence, curr_pc = 0x%0x", curr_pc), UVM_HIGH);
                                inst_arr.delete(curr_pc);
                                break;
                            end
                        end
                    end
                    else begin
                        exit_pc = curr_pc;
                        re_loop = 1;
                    end

                    if (re_loop == 1) begin
                        curr_pc = init_start_pc;
                  back_br_arr.delete;
                        pc_arr.delete;
                        accessed_lsu_pa_arr.delete;
                      for (int i=0; i<32; i++) begin
                        m_gpr[i] = 0;
                      end
                        loop_retry = 0;
                      init_m_mem();
                        init_csr();
                        if (re_randomize == 1) begin
                            if (inst_arr.first(loop_pc)) 
                    do begin
                                if (!m_boot_pc.exists(loop_pc) && !m_tvec_pc.exists(loop_pc)) begin
                        inst_arr.delete(loop_pc);
                      end
                    end while (inst_arr.next(loop_pc));
                        end
                        continue;
                    end
                end
            end
        end
        // add one more inst for fpu store inst
        else if (inst_arr[curr_pc].inst_type inside {OP_FSW} && inst_arr[curr_pc].fpu_inst_is_fixed !=1 && ((curr_pc +4) == next_pc || (curr_pc +4) != next_pc && cause ==`RISCV_CSR_MCAUSE_EXCODE_SPAGE_FAULT) ) begin
                // create an inst
                `uvm_info("debug", $psprintf("add one more inst for fpu fsw inst"), UVM_HIGH);
                inst_arr[curr_pc].fpu_inst_is_fixed =1;//set flag
                txn = riscv_inst_base_txn::type_id::create("txn",,get_full_name());
                void'(txn.randomize());
                txn.inst_type = OP_SW;
                txn.rs1 = inst_arr[curr_pc].rs1;
                txn.imm = inst_arr[curr_pc].imm;
                txn.is_key_inst = 1;
                txn.pc = curr_pc + 4;
                gen_fixed_inst(txn);
                store_inst_code(txn);
        end
        // if 2 byte from next_pc has fetch violation, then next pc must have fetch exception
    else if (check_mem_trans_access_violation(next_pc, 2, 1, 0) == 1) begin
            if (next_pc == m_curr_mmode_trap_vector || next_pc == m_curr_smode_trap_vector) begin
                `uvm_info("debug", $psprintf("special situation, trap vector self has exception due to U-mode access"), UVM_HIGH);
            end
            else if (!inst_arr.exists(next_pc)) begin
                // create a dummy op for next_pc
                `uvm_info("debug", $psprintf("JALR target has memory access violation, create a dummy op for next_pc"), UVM_HIGH);
                txn = riscv_inst_base_txn::type_id::create("txn",,get_full_name());
                void'(txn.randomize());
                txn.pc = next_pc;
                txn.pc_pa.push_back('hdeadbeef_deadbeef_deadbeef_deadbeef_deadbeef_deadbeef_deadbeef_deadbeef);
        txn.is_dummy_inst = 1;
                inst_arr[txn.pc] = txn;
            end
        end
        else if (!inst_arr.exists(next_pc)) begin
      // check if 4 byte from next_pc have fetch violation or existing insturction override, which decides whether 4byte inst can be inserted
            valid_next_pc_bytes = 0;
            for (int i=0; i<4; i++) begin
          if (check_mem_trans_access_violation_per_byte(next_pc+i, 1, 0) == 1) begin
                    break;
                end
                else begin
                    target_pc = {};
                    if (is_overlap_with_exist_pc(next_pc+i, 1, 1, target_pc) == 1) begin
                        break;
                    end
                    else begin
                        valid_next_pc_bytes++;
                    end
                end
            end

      if (valid_next_pc_bytes == 2) begin
        gen_inst_32_en = 0;
      end
      else if (valid_next_pc_bytes == 4) begin
        gen_inst_32_en = 1;
      end
            else if (valid_next_pc_bytes == 0) begin
                `uvm_info("debug", $psprintf("There is 0 valid_next_pc_bytes to insert, re-randomize, curr_pc = 0x%0x, next_pc = 0x%0x", curr_pc, next_pc), UVM_HIGH);
                return 1;
            end
            else begin
                `uvm_fatal("fatal", $psprintf("impossible case, valid_next_pc_bytes = %0d, curr_pc = 0x%0x, next_pc = 0x%0x", valid_next_pc_bytes, curr_pc, next_pc));
            end
            
      txn = gen_inst(next_pc, gen_inst_32_en, gen_fail);
      if (gen_fail == 1) begin
        `uvm_info("debug", $psprintf("Got gen fail for gen_inst(), re-randomize, curr_pc = 0x%0x, next_pc = 0x%0x", curr_pc, next_pc), UVM_HIGH);
        return 1;
      end

            // NEED_CHANGE, update as needed
      //insert_fetch_bus_fault(next_pc, get_fetch_size(txn.inst_type));

            store_inst_code(txn);
            loop_retry = 1;  // it's possible that previous inst load this inst code addr
            `uvm_info("debug", $psprintf("gen a normal inst for non-exist next_pc, pc = 0x%0x, inst_type = 0x%0x, rd = %0d, rs1 = %0d, rs2 = %0d, imm = 0x%0x", next_pc, txn.inst_type, txn.rd, txn.rs1, txn.rs2, txn.imm), UVM_HIGH);
        end


        // additional check if we can exist loop for done generating
        if (pc_arr.num() == inst_num) begin
            if (m_tvec_pc.exists(next_pc) || check_fetch_fault_exception(next_pc, get_fetch_size(inst_arr[next_pc].inst_type)) == 1) begin
                inst_num++;
            end
            else begin
                next_pc_pa_whole = 0;
                for (int i=0; i<inst_arr[next_pc].inst_bin_code_size; i++) begin
          next_pc_pa_whole[64*i+:64] = va2pa(next_pc+i, 1);
        end
                // insert JAL for end pc, so code size is 4
                if (is_pc_accessed_by_lsu(next_pc_pa_whole, 4) == 1) begin
                    inst_num++;
                    `uvm_info("debug", $psprintf("last exit pc is accessed by prevous lsu before, pc = 0x%0x, pc_pa = 0x%0x", next_pc, next_pc_pa_whole), UVM_HIGH);
                end
            end
        end

        // last instruction in specified number of sequence
        // since for extra inst, no immediate retry due to performance concern
        // there is chance extra inst bin_code has been modified by other LSU inst, so need to re-check whole sequence again
        if (pc_arr.num() == inst_num && loop_retry == 1) begin
            `uvm_info("debug", $psprintf("whole sequence has been generated but there is un-checked extra inst, re-loop to check again"), UVM_HIGH);
            insert_inst_for_unexecuted_addr();
            curr_pc = init_start_pc;
      back_br_arr.delete;
            pc_arr.delete;
            accessed_lsu_pa_arr.delete;
          for (int i=0; i<32; i++) begin
            m_gpr[i] = 0;
          end
            loop_retry = 0;
          init_m_mem();
            init_csr();
            continue;
        end

    curr_pc = next_pc;
  end

    last_pc = curr_pc;
    return 0;
endfunction

// PA decoder to get PA range
// NEED_CHANGE
function riscv_base_seq::pa_range_e riscv_base_seq::get_pa_range(bit[63:0] pa);
  return PA_RANGE_RSVD;
endfunction

// convert VA to PA
// NEED_CHANGE
function bit[63:0] riscv_base_seq::va2pa(bit[63:0] va, bit is_fetch);
  return va;
endfunction

// convert PA to VA
// NEED_CHANGE
function bit[63:0] riscv_base_seq::pa2va(bit[63:0] pa, bit is_fetch);
  return pa;
endfunction

// check if there is memory translation violation or pa access violation per access (multiple byte)
// return 0 if no violation, return 1 if there is violation
// NEED_CHANGE
function bit riscv_base_seq::check_mem_trans_access_violation(bit[63:0] va, int size, bit is_fetch, bit is_load);
  bit [63:0] pa;
  bit [63:0] pa_queue[$];

  for (int i=0; i<size; i++) begin
    if (check_mem_trans_access_violation_per_byte(va+i, is_fetch, is_load) == 1) begin
      return 1;
    end
        else begin
          pa = va2pa(va+i, is_fetch);
            pa_queue.push_back(pa);
        end
  end

	// NEED_CHANGE, check if this is needed
  //if (check_pmp_cross_boundary(pa_queue) == 1) begin
  //  return 1;
  //end

  return 0;
endfunction

// check if there is memory translation violation or pa access violation per byte
// return 0 if no violation, return 1 if there is violation
// NEED_CHANGE
function bit riscv_base_seq::check_mem_trans_access_violation_per_byte(bit[63:0] va, bit is_fetch, bit is_load);
    bit [63:0] pa;

    pa = va2pa(va, is_fetch);

    // check pa access violation here

    // check PMP violation
	// NEED_CHANGE, check if this is needed
    //if (check_pmp_violation(pa, is_fetch, is_load, 1) == 1) begin
    //    return 1;
    //end

    return 0;
endfunction

// check if there is page fault exception
// return 0 if no violation, return 1 if there is violation
// NEED_CHANGE
function bit riscv_base_seq::check_page_fault_violation(bit[63:0] va, int size, bit is_fetch, bit is_load);
  return 0;
endfunction

// check if there is pmp violation
// return 0 if no violation, return 1 if there is violation
function bit riscv_base_seq::check_pmp_violation(bit[63:0] pa, bit is_fetch, bit is_load, int size);

    privilege_level_e curr_chk_priv_level;
    bit found_pa;
    bit part_hit;
    int i;
    bit[63:0] min_addr;
    bit[65:0] max_addr;

    curr_chk_priv_level = get_curr_check_priv_level(is_fetch);


    for (i=0; i<`MAX_PMP_NUM; i++) begin
         if(m_init_pmpcfg_cfg[i].a != `PMP_OFF) begin
             min_addr = m_init_pmpaddr_cfg[i].min_addr;
             max_addr = min_addr + m_init_pmpaddr_cfg[i].range;
             if(m_init_pmpcfg_cfg[i].a == `PMP_TOR) begin
                 //TOR mode
                 min_addr = m_init_pmpaddr_cfg[i].min_addr;
                 max_addr = m_init_pmpaddr_cfg[i].max_addr;
                 if(i==0) min_addr = 0;
             end
             if(pa inside {[min_addr:max_addr-1]})
                 found_pa = 1;

             if(found_pa ) break;
         end
    end
    if(~(found_pa) && (curr_chk_priv_level == PRIV_LEVEL_MMODE)) return 0;  //miss, mmode
    else if(~(found_pa) && (curr_chk_priv_level != PRIV_LEVEL_MMODE)) return 1; //miss, s/u mode

    //found_pa==1
    if((curr_chk_priv_level == PRIV_LEVEL_MMODE) && !m_init_pmpcfg_cfg[i].l) begin
        return 0;
    end

    if (is_fetch == 1) begin
        if (m_init_pmpcfg_cfg[i].x == 0) begin
            return 1;
        end
    end
    else begin
        if (is_load == 1) begin
            if (m_init_pmpcfg_cfg[i].r == 0) begin
                return 1;
            end
        end
        else begin
            if (m_init_pmpcfg_cfg[i].w == 0) begin
                return 1;
            end
        end
    end

    return 0;
endfunction

// return 0 if no violation, return 1 if there is violation
function bit riscv_base_seq::check_pmp_cross_boundary(bit[63:0] pa_queue[$]);
    bit found_pa=0;
    int i;
    bit[63:0] min_addr;
    bit[65:0] max_addr;

    for (i=0; i<`MAX_PMP_NUM; i++) begin
         if(m_init_pmpcfg_cfg[i].a != `PMP_OFF) begin
             min_addr = m_init_pmpaddr_cfg[i].min_addr;
             max_addr = min_addr + m_init_pmpaddr_cfg[i].range;
             if(m_init_pmpcfg_cfg[i].a == `PMP_TOR) begin
                 //TOR mode
                 min_addr = m_init_pmpaddr_cfg[i].min_addr;
                 max_addr = m_init_pmpaddr_cfg[i].max_addr;
                 if(i==0) min_addr = 0;
             end

             for (int j=0; j<pa_queue.size(); j++) begin
                 if (pa_queue[j] inside {[min_addr:max_addr-1]}) begin
                     if (j == 0) begin
                         found_pa = 1;
                     end
                     else if (found_pa != 1) begin
                         return 1;
                     end
                 end
                 else if (found_pa != 0) begin
                     return 1;
                 end
             end
             if(found_pa == 1) break;
         end
    end
    return 0;
endfunction



// get PA
// NEED_CHANGE
function bit[63:0] riscv_base_seq::get_pa(bit[63:0] va, bit is_fetch, bit is_load);
    bit [63:0] pa;

    pa = va2pa(va, is_fetch);
    return pa;
endfunction

// insert valid instruction code for unexecuted addr in one 8-byte fetch packet
function void riscv_base_seq::insert_inst_for_unexecuted_addr();
    bit [63:0] addr;
    bit [63:0] check_addr;
    bit [63:0] check_addr_1;
    bit found_in_m_mem;
    bit found_in_dut_mem;
    riscv_inst_base_txn txn;
    bit has_4byte_room;
    bit has_2byte_room;
  bit [255:0] pc_pa;

    if (riscv_mem::dut_mem.first(addr))
    do begin
        check_addr = {addr[63:3], ~addr[2], addr[1:0]};
        if (!riscv_mem::dut_mem.exists(check_addr)) begin
            // check whether the nearby 2 byte are all not existed in dut_mem/m_mem
            found_in_m_mem = 0;
            found_in_dut_mem = 0;
            for (int i=0; i<2; i++) begin
                check_addr_1 = (check_addr[63:1] << 1) + i;
                if (riscv_mem::dut_mem.exists(check_addr_1)) begin
                    found_in_dut_mem = 1;
                end
                if (m_mem.exists(check_addr_1)) begin
                    found_in_m_mem = 1;
                end
            end

            if (found_in_m_mem == 0 && found_in_dut_mem == 0) begin
                has_2byte_room = 1;
            end
            else begin
                has_2byte_room = 0;
            end

            // check whether the nearby 4 byte are all not existed in dut_mem/m_mem
            found_in_m_mem = 0;
            found_in_dut_mem = 0;
            for (int i=0; i<4; i++) begin
                check_addr_1 = (check_addr[63:2] << 2) + i;
                if (riscv_mem::dut_mem.exists(check_addr_1)) begin
                    found_in_dut_mem = 1;
                end
                if (m_mem.exists(check_addr_1)) begin
                    found_in_m_mem = 1;
                end
            end

            if (found_in_m_mem == 0 && found_in_dut_mem == 0) begin
                has_4byte_room = 1;
            end
            else begin
                has_4byte_room = 0;
            end

            // insert a valid inst (16 or 32) in this 4-byte addr
            if (has_4byte_room == 1) begin
                check_addr_1 = (check_addr[63:2] << 2) + 0;
                txn = new();
                void'(txn.randomize());
                void'(txn.gen_inst_bin_code());
        pc_pa = 0;
                for (int i=0; i<txn.inst_bin_code_size; i++) begin
          pc_pa[64*i+:64] = check_addr_1+i;
                    riscv_mem::dut_mem[check_addr_1+i] = txn.inst_bin_code[8*i+:8];
                    riscv_mem::rm_mem[check_addr_1+i] = txn.inst_bin_code[8*i+:8];
                    m_init_mem[check_addr_1+i] = txn.inst_bin_code[8*i+:8];
                    m_mem[check_addr_1+i] = txn.inst_bin_code[8*i+:8];
                    `uvm_info("debug", $psprintf("insert_inst_for_unexecuted_addr, addr = 0x%0x, data = 0x%0x", check_addr_1+i, m_init_mem[check_addr_1+i]), UVM_DEBUG);
                end
                txn.pc_pa.push_back(pc_pa);
            end
            // insert a 16bit valid inst in this 2-byte addr
            else if (has_2byte_room == 1) begin
                check_addr_1 = (check_addr[63:1] << 1) + 0;
                txn = new();
                void'(txn.randomize() with {
                    inst_type > OP_ILLEGAL;  // 16bit inst
                });
                void'(txn.gen_inst_bin_code());
        pc_pa = 0;
                for (int i=0; i<2; i++) begin
          pc_pa[64*i+:64] = check_addr_1+i;
                    riscv_mem::dut_mem[check_addr_1+i] = txn.inst_bin_code[8*i+:8];
                    riscv_mem::rm_mem[check_addr_1+i] = txn.inst_bin_code[8*i+:8];
                    m_init_mem[check_addr_1+i] = txn.inst_bin_code[8*i+:8];
                    m_mem[check_addr_1+i] = txn.inst_bin_code[8*i+:8];
                    `uvm_info("debug", $psprintf("insert_inst_for_unexecuted_addr, addr = 0x%0x, data = 0x%0x", check_addr_1+i, m_init_mem[check_addr_1+i]), UVM_DEBUG);
                end
                txn.pc_pa.push_back(pc_pa);
            end
        end
    end while (riscv_mem::dut_mem.next(addr));
endfunction

function bit[1:0] riscv_base_seq::rand_two_bits();
    bit [1:0] value;

    value = $urandom();

    return value;
endfunction

function bit riscv_base_seq::is_pc_accessed_by_lsu(bit[255:0] pc_pa, int code_size);
    bit is_accessed = 0;

    for (int i=0; i<code_size; i++) begin
        if (accessed_lsu_pa_arr.exists(pc_pa[64*i+:64])) begin
            is_accessed = 1;
        end
    end

    return is_accessed;
endfunction

function riscv_base_seq::privilege_level_e riscv_base_seq::get_curr_check_priv_level(bit is_fetch);
    privilege_level_e curr_chk_priv_level;

    if (mprv == 1 && is_fetch == 0) begin
        // TODO: review with Neo Fang
        //       this static cast is a compile-time operation and may fail at run-time.
        curr_chk_priv_level = privilege_level_e'(mpp); // TODO: review with Neo Fang
    end
    else begin
        curr_chk_priv_level = m_curr_priv_level;
    end

    return curr_chk_priv_level;
endfunction

`endif // RISCV_BASE_SEQ__SV
