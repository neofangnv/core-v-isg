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

`ifndef RISCV_MEM__SV
`define RISCV_MEM__SV

class riscv_mem extends uvm_component;
	static bit [7:0] dut_mem [*];
	static bit [7:0] rm_mem [*];

	`uvm_component_utils(riscv_mem);

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
		bit [7:0] tmp_mem [*];
		bit [63:0] addr;

	    $readmemb(filename, tmp_mem);

		if (tmp_mem.first(addr))
		do begin
			dut_mem[addr+start_addr] = tmp_mem[addr];
			rm_mem[addr+start_addr] = tmp_mem[addr];
		end while (tmp_mem.next(addr));
	endfunction
	
	function void mem_loadh(string filename, bit[63:0] start_addr=0);
		bit [7:0] tmp_mem [*];
		bit [63:0] addr;
        string str;
        int fh;
        bit [7:0] data;

        fh = $fopen(filename, "r");
        if (fh == 0) begin
            `uvm_fatal("fatal", $psprintf("can't open file %s", filename));
        end

        addr = 0;
        while (!$feof(fh)) begin
            $fgets(str, fh);
            if (str[0] == "@") begin
                $sscanf(str, "@%x", addr);
            end
            else begin
                $sscanf(str, "%x", data);
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

		if (dut_mem.first(addr))
		do begin
			tmp_mem[addr-start_addr] = dut_mem[addr];
		end while (dut_mem.next(addr));

	    $writememb(filename, tmp_mem);
	endfunction

	function void mem_storeh(string filename, bit[63:0] start_addr=0);
		bit [7:0] tmp_mem [*];
		bit [63:0] addr;

		if (dut_mem.first(addr))
		do begin
			tmp_mem[addr-start_addr] = dut_mem[addr];
		end while (dut_mem.next(addr));

	    $writememh(filename, tmp_mem);
	endfunction

endclass: riscv_mem

`endif // RISCV_MEM__SV
