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

VCS                = VCS
VCS_HOME          ?=
VCS_CMP_FLAGS     ?=
VCS_UVM_ARGS      ?=
VCS_RESULTS       ?=
VCS_RUN_FLAGS     ?=

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

no_rule:
	@echo 'makefile: SIMULATOR is set to $(SIMULATOR), but no rule/target specified.'
	@echo 'try "make SIMULATOR=vcs comp" (or just "make comp" if shell ENV variable SIMULATOR is already set).'

all: clean_all comp

help:
	vcs -help

# VCS compile target
comp: mk_results
	$(VCS) \
		$(VCS_CMP_FLAGS) \
		$(VCS_UVM_ARGS) \
		$(VCS_ACC_FLAGS) \
		-sv_lib $(UVM_HOME)/src/dpi/libuvm_dpi.so \
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
		+$(UVM_PLUSARGS)

clean_all:
	rm -rf $(VCS_RESULTS)
