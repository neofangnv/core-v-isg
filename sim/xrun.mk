###############################################################################
#
# Copyright 2020 OpenHW Group
# 
# Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# You may obtain a copy of the License at
# 
#     https://solderpad.org/licenses/
# 
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.
# 
###############################################################################

XRUN              = xrun
XRUN_UVMHOME_ARG ?= CDNS-1.2-ML
XRUN_CMP_FLAGS   ?= -64bit -disable_sem2009 -access +rwc -q -clean -sv -uvm -uvmhome $(XRUN_UVMHOME_ARG)
XRUN_DIR         ?= xcelium.d

# Variables to control wave dumping from command the line
# Humans _always_ forget the "S", so you can have it both ways...
WAVES                  ?= 0
WAVE                   ?= 0
DUMP_WAVES             := 0

ifneq ($(WAVES), 0)
DUMP_WAVES = 1
endif

ifneq ($(WAVE), 0)
DUMP_WAVES = 1
endif

ifneq ($(DUMP_WAVES), 0)
XRUN_ACC_FLAGS ?= +acc
XRUN_DMP_FILE  ?= 
XRUN_DMP_FLAGS ?= -waves $(XRUN_DMP_FILE)
endif


.PHONY: comp

no_rule:
	@echo 'makefile: SIMULATOR is set to $(SIMULATOR), but no rule/target specified.'
	@echo 'try "make SIMULATOR=xrun comp" (or just "make comp" if shell ENV variable SIMULATOR is already set).'

all: clean_all comp

help:
	xrun -help

# XRUN compile target
comp:
	$(XRUN) \
		$(XRUN_CMP_FLAGS) \
		$(XRUN_ACC_FLAGS) \
		+incdir+../memory \
		+incdir+../parameter \
		+incdir+../sequence \
		+incdir+../transaction \
		./CV32E40P_macros.sv \
		../transaction/riscv_txn_pkg.sv \
		../memory/riscv_memory_pkg.sv \
		../parameter/riscv_params.sv \
		../sequence/riscv_base_seq.sv \
		../sequence/riscv_random_all_seq.sv \
		+$(UVM_PLUSARGS) \
		-elaborate

clean_all:
	rm -rf $(XRUN_DIR)
	rm -f  xrun.history
	rm -f  xrun.log
