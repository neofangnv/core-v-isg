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

`ifndef RISCV_MEM__SV
`define RISCV_MEM__SV

class riscv_mem extends uvm_component;
  static bit [7:0] dut_mem [*];
  static bit [7:0] rm_mem [*];

  `uvm_component_utils(riscv_mem)

  function new(string name = "riscv_mem", uvm_component parent);
    super.new(name,parent);
  endfunction: new

  function void fill_mem(bit[255:0] addr, bit[31:0] data, int size);
    for (int i=0; i<size; i++) begin
      dut_mem[addr[64*i+:64]] = data[8*i +: 8];
      rm_mem[addr[64*i+:64]] = data[8*i +: 8];
      `uvm_info("RISCV_MEM_FILL", $psprintf("filling mem addr = 0x%0x, data = 0x%0x", addr[64*i+:64], data[8*i +: 8]), UVM_HIGH);
    end
  endfunction: fill_mem

  function void dump_dut_mem();
    bit [63:0] addr;

    if (dut_mem.first(addr))
    do begin
      `uvm_info("RISCV_DUT_MEM_DUMP", $psprintf("addr = 0x%0x, data = 0x%0x", addr, dut_mem[addr]), UVM_HIGH);
    end while (dut_mem.next(addr));
  endfunction: dump_dut_mem

  function void dump_rm_mem();
    bit [63:0] addr;

    if (rm_mem.first(addr))
    do begin
      `uvm_info("RISCV_RM_MEM_DUMP", $psprintf("addr = 0x%0x, data = 0x%0x", addr, rm_mem[addr]), UVM_HIGH);
    end while (rm_mem.next(addr));
  endfunction: dump_rm_mem

  ///////////////////////
  // mem load/store
  ///////////////////////
  function void mem_loadb(string filename, bit[63:0] start_addr=0);
    bit [63:0] addr;
    bit [7:0] tmp_mem [*];

`ifndef DSIM
    // DSIM says: "Second argument to $readmem/$writemem task must be an integral array"
    $readmemb(filename, tmp_mem);
`else
    bit [7:0] dsim_mem [1000000];
    $readmemb(filename, dsim_mem);
    for (int i=0; i<1000000; i++) begin
      if (dsim_mem[i] === 8'hXX) begin
        break;
      end
      else begin
        tmp_mem[i] = dsim_mem[i];
      end
    end
`endif

    if (tmp_mem.first(addr))
    do begin
      dut_mem[addr+start_addr] = tmp_mem[addr];
      rm_mem[addr+start_addr] = tmp_mem[addr];
    end while (tmp_mem.next(addr));
  endfunction
  
  function void mem_loadh(string filename, bit[63:0] start_addr=0);
//`ifdef DSIM
//    bit [7:0] tmp_mem [1000000];
//`else
    bit [7:0] tmp_mem [*];
//`endif
    bit [63:0] addr;
        string str;
        int fh;
        bit [7:0] data;
		int code;

        fh = $fopen(filename, "r");
        if (fh == 0) begin
            `uvm_fatal("fatal", $psprintf("can't open file %s", filename));
        end

        addr = 0;
        while (!$feof(fh)) begin
            code = $fgets(str, fh);
            if (str[0] == "@") begin
                code = $sscanf(str, "@%x", addr);
            end
            else begin
                code = $sscanf(str, "%x", data);
                tmp_mem[addr] = data;
                addr++;
            end
        end

        $fclose(fh);

      //$readmemh(filename, tmp_mem);

    if (tmp_mem.first(addr))
    do begin
      dut_mem[addr+start_addr] = tmp_mem[addr];
      rm_mem[addr+start_addr] = tmp_mem[addr];
    end while (tmp_mem.next(addr));
  endfunction

  function void mem_storeb(string filename, bit[63:0] start_addr=0);
    bit [7:0] tmp_mem [*];
    bit [63:0] addr;

`ifndef DSIM
    if (dut_mem.first(addr))
    do begin
      tmp_mem[addr-start_addr] = dut_mem[addr];
    end while (dut_mem.next(addr));
    // DSIM says: "Second argument to $readmem/$writemem task must be an integral array"
    $writememb(filename, tmp_mem);
`else
    int i = 0;
    bit [7:0] dsim_mem [1000000];
    do begin
      dsim_mem[i++] = dut_mem[addr];
    end while (dut_mem.next(addr));
    $writememb(filename, dsim_mem);
`endif

  endfunction

  function void mem_storeh(string filename, bit[63:0] start_addr=0);
    bit [7:0] tmp_mem [*];
    bit [63:0] addr;

`ifndef DSIM
    if (dut_mem.first(addr)) begin
      do begin
        tmp_mem[addr-start_addr] = dut_mem[addr];
      end while (dut_mem.next(addr));
    end
    // DSIM says: "Second argument to $readmem/$writemem task must be an integral array"
    $writememh(filename, tmp_mem);
`else
    int i = 0;
    bit [7:0] dsim_mem [1000000];
    do begin
      dsim_mem[i++] = dut_mem[addr];
    end while (dut_mem.next(addr));
    $writememh(filename, dsim_mem);
`endif
  endfunction

endclass: riscv_mem

`endif // RISCV_MEM__SV
