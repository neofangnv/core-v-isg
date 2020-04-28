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
#
# Common Makefile for the core-v-isg.
#
###############################################################################

# "Constants"
MAKE           = make
.DEFAULT_GOAL := no_rule 

# Compile compile flags for all simulators (careful!)
WAVES        ?= 0
SV_CMP_FLAGS ?= 
TIMESCALE    ?= -timescale 1ns/1ps
UVM_PLUSARGS ?=

# User selectable simulator targets/rules
SIMULATOR    ?= unsim 

###############################################################################
# Include the targets/rules for the selected SystemVerilog simulator
#
ifeq ($(SIMULATOR), dsim)
include dsim.mk
else
ifeq ($(SIMULATOR), xrun)
include xrun.mk
else
ifeq ($(SIMULATOR), vsim)
include vsim.mk
else
ifeq ($(SIMULATOR), vcs)
include vcs.mk
else
include unsim.mk
endif
endif
endif
endif
