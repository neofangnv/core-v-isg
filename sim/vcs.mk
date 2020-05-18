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

VCS                = vcs
VCS_HOME          ?=
VCS_CMP_LOG       ?= comp.log
VCS_CMP_FLAGS     ?= -sverilog
VCS_UVM_ARGS      ?= -ntb_opts uvm
VCS_RESULTS       ?= csrc simv.daidir vc_hdrs.h
VCS_TARGET        ?= simv
VCS_RUN_FLAGS     ?= +UVM_MAX_QUIT_COUNT=50
VCS_RUN_LOG       ?= run.log
TEST_NAME         ?= riscv_random_all_test
SEED              ?= 0
UVM_VERBOSITY     ?= UVM_LOW
GEN_INST_NUM      ?= 1000
RUN_ARGS          ?=

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
VCS__ACC_FLAGS ?= +acc
VCS__DMP_FILE  ?= 
VCS__DMP_FLAGS ?= -waves $(VCS_DMP_FILE)
endif


.PHONY: comp

val = 0

no_rule:
	@echo 'makefile: SIMULATOR is set to $(SIMULATOR), but no rule/target specified.'
	@echo 'try "make SIMULATOR=vcs comp" (or just "make comp" if shell ENV variable SIMULATOR is already set).'
	@echo 'THIS MAKEFILE NOT YET IMPLEMENTED.'
	exit $(val)

all: clean_all comp

help:
	vcs -help

# VCS compile target
comp:
	$(VCS) \
		-l $(VCS_CMP_LOG) \
		-o $(VCS_TARGET) \
		$(VCS_CMP_FLAGS) \
		$(VCS_UVM_ARGS) \
		+incdir+../memory \
		+incdir+../parameter \
		+incdir+../sequence \
		+incdir+../transaction \
		+incdir+../test \
		./CV32E40P_macros.sv \
		../transaction/riscv_txn_pkg.sv \
		../memory/riscv_memory_pkg.sv \
		../parameter/riscv_params.sv \
		../sequence/riscv_base_seq.sv \
		../sequence/riscv_random_all_seq.sv \
		../test/riscv_test_base.sv \
		../test/riscv_random_all_test.sv \
		../test/riscv_gen_top.sv \

clean_all:
	rm -rf $(VCS_RESULTS)
	rm -rf $(VCS_TARGET)
	rm -rf $(VCS_CMP_LOG)

run:
	$(VCS_TARGET) \
		-l $(VCS_RUN_LOG) \
		+UVM_TESTNAME=$(TEST_NAME) \
		+ntb_random_seed=$(SEED) \
		+UVM_VERBOSITY=$(UVM_VERBOSITY) \
		+MAXLEN=$(GEN_INST_NUM) +MINLEN=$(GEN_INST_NUM) \
		$(RUN_ARGS) \
		$(VCS_RUN_FLAGS) \
