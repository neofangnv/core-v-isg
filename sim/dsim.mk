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
# DSIM-specific Makefile for the CV32E40P "uvmt_cv32" testbench.
# DSIM is the Metrics Technologies SystemVerilog simulator  (https://metrics.ca/)
#
###############################################################################

DSIM                    = dsim
DSIM_HOME              ?= /tools/Metrics/dsim
DSIM_CMP_FLAGS         ?= $(TIMESCALE) $(SV_CMP_FLAGS)
DSIM_UVM_ARGS          ?= +incdir+$(UVM_HOME)/src $(UVM_HOME)/src/uvm_pkg.sv
DSIM_RESULTS           ?= $(PWD)/dsim_results
DSIM_WORK              ?= $(DSIM_RESULTS)/dsim_work
DSIM_IMAGE             ?= dsim.out
DSIM_RUN_FLAGS         ?=

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
DSIM_ACC_FLAGS ?= +acc
DSIM_DMP_FILE  ?= dsim.fst
DSIM_DMP_FLAGS ?= -waves $(DSIM_DMP_FILE)
endif


.PHONY: sim

no_rule:
	@echo 'makefile: SIMULATOR is set to $(SIMULATOR), but no rule/target specified.'
	@echo 'try "make SIMULATOR=dsim sanity" (or just "make sanity" if shell ENV variable SIMULATOR is already set).'
#	@echo 'DUMP_WAVES=$(DUMP_WAVES)   DSIM_ACC_FLAGS=$(DSIM_ACC_FLAGS)   DSIM_DMP_FLAGS=$(DSIM_DMP_FLAGS)'

# The sanity test is defined in ../Common.mk and will change over time
#sanity: hello-world

all: clean_all sanity

help:
	dsim -help

mk_results: 
	$(MKDIR_P) $(DSIM_RESULTS)
	$(MKDIR_P) $(DSIM_WORK)

# DSIM compile target
#      - TODO: cd $(DSIM_RESULTS) - incompatible with pkg file
comp: mk_results $(CV32E40P_PKG)
	$(DSIM) \
		$(DSIM_CMP_FLAGS) \
		$(DSIM_UVM_ARGS) \
		$(DSIM_ACC_FLAGS) \
		-sv_lib $(UVM_HOME)/src/dpi/libuvm_dpi.so \
		+incdir+$(DV_UVME_CV32_PATH) \
		+incdir+$(DV_UVMT_CV32_PATH) \
		-f $(CV32E40P_MANIFEST) \
		-f $(DV_UVMT_CV32_PATH)/uvmt_cv32.flist \
		-work $(DSIM_WORK) \
		+$(UVM_PLUSARGS) \
		-genimage $(DSIM_IMAGE)

no-firmware: comp
	mkdir -p $(DSIM_RESULTS)/hello_world && cd $(DSIM_RESULTS)/hello_world  && \
	$(DSIM) -l dsim-$(UVM_TESTNAME).log -image $(DSIM_IMAGE) \
		-work $(DSIM_WORK) $(DSIM_RUN_FLAGS) $(DSIM_DMP_FLAGS) \
		-sv_lib $(UVM_HOME)/src/dpi/libuvm_dpi.so \
		+UVM_TESTNAME=$(UVM_TESTNAME)
#		+verbose

####
# The 'custom test': this target provides the ability to specify both the
#                    testcase run by the UVM environment and a C program to
#                    be executed by the core. Note that this UVM testcase is
#                    expected to load the compiled program into the core's memory.
#
# User defined variables used by this target:
#   CUSTOM_DIR:   Absolute, not relative, path to the custom C program. Default
#                 is `pwd`/../../tests/core/custom.
#   CUSTOM_PROG:  C program that executes on the core. Default is hello_world.c.
#   UVM_TESTNAME: Class identifer (not file path) of the UVM testcase run by
#                 environment. Default is uvmt_cv32_firmware_test_c.
#
# Use cases:
#   1: Full specification of the hello-world test:
#      $ make custom SIMULATOR=dsim CUSTOM_DIR=`pwd`/../../tests/core/custom CUSTOM_PROG=hello_world UVM_TESTNAME=uvmt_cv32_firmware_test_c
#
#   2: Same thing, using the defaults in these Makefiles:
#      $ make custom
#
#   3: Run your own "custom program"
#      $ make custom CUSTOM_PROG=<my_C_program>
#
custom: comp $(CUSTOM_DIR)/$(CUSTOM_PROG).hex
	mkdir -p $(DSIM_RESULTS)/hello_world && cd $(DSIM_RESULTS)/hello_world  && \
	$(DSIM) -l dsim-$(CUSTOM_PROG).log -image $(DSIM_IMAGE) \
		-work $(DSIM_WORK) $(DSIM_RUN_FLAGS) $(DSIM_DMP_FLAGS) \
		-sv_lib $(UVM_HOME)/src/dpi/libuvm_dpi.so \
		+UVM_TESTNAME=$(UVM_TESTNAME) \
		+firmware=$(CUSTOM_DIR)/$(CUSTOM_PROG).hex

####
# Commonly used targets:
#
hello-world: comp $(CUSTOM)/hello_world.hex
	mkdir -p $(DSIM_RESULTS)/hello_world && cd $(DSIM_RESULTS)/hello_world  && \
	$(DSIM) -l dsim-hello_world.log -image $(DSIM_IMAGE) \
		-work $(DSIM_WORK) $(DSIM_RUN_FLAGS) $(DSIM_DMP_FLAGS) \
		-sv_lib $(UVM_HOME)/src/dpi/libuvm_dpi.so \
		+UVM_TESTNAME=uvmt_cv32_firmware_test_c \
		+firmware=$(CUSTOM)/hello_world.hex
#		+verbose

# Runs tests in riscv_tests/ only
cv32-riscv-tests: comp $(CV32_RISCV_TESTS_FIRMWARE)/cv32_riscv_tests_firmware.hex
	mkdir -p $(DSIM_RESULTS)/riscv-tests && cd $(DSIM_RESULTS)/riscv-tests && \
	$(DSIM) -l dsim-riscv_tests.log -image $(DSIM_IMAGE) \
		-work $(DSIM_WORK) $(DSIM_RUN_FLAGS) $(DSIM_DMP_FLAGS) \
		-sv_lib $(UVM_HOME)/src/dpi/libuvm_dpi.so \
		+UVM_TESTNAME=uvmt_cv32_firmware_test_c \
		+firmware=$(CV32_RISCV_TESTS_FIRMWARE)/cv32_riscv_tests_firmware.hex

# Runs tests in riscv_compliance_tests/ only
cv32-riscv-compliance-tests: comp $(CV32_RISCV_COMPLIANCE_TESTS_FIRMWARE)/cv32_riscv_compliance_tests_firmware.hex
	mkdir -p $(DSIM_RESULTS)/riscv-compliance && cd $(DSIM_RESULTS)/riscv-compliance && \
	$(DSIM) -l dsim-riscv_compliance_tests.log -image $(DSIM_IMAGE) \
		-work $(DSIM_WORK) $(DSIM_RUN_FLAGS) $(DSIM_DMP_FLAGS) \
		-sv_lib $(UVM_HOME)/src/dpi/libuvm_dpi.so \
		+UVM_TESTNAME=uvmt_cv32_firmware_test_c \
		+firmware=$(CV32_RISCV_COMPLIANCE_TESTS_FIRMWARE)/cv32_riscv_compliance_tests_firmware.hex

# Runs all tests in riscv_tests/ and riscv_compliance_tests/
cv32-firmware: comp $(FIRMWARE)/firmware.hex
	mkdir -p $(DSIM_RESULTS)/firmware && cd $(DSIM_RESULTS)/firmware && \
	$(DSIM) -l dsim-firmware.log -image $(DSIM_IMAGE) \
		-work $(DSIM_WORK) $(DSIM_RUN_FLAGS) $(DSIM_DMP_FLAGS) \
		-sv_lib $(UVM_HOME)/src/dpi/libuvm_dpi.so \
		+UVM_TESTNAME=uvmt_cv32_firmware_test_c \
		+firmware=$(FIRMWARE)/firmware.hex

###############################################################################
# DSIM UNIT TESTS: run each test individually.
#                  Example: to run the ADDI test `make dsim-unit-test addi`
# DO NOT INVOKE rule "dsim-firmware-unit-test" directly.   It is a support
# rule for rule "dsim-unit-test" (in included ../Firmware.mk).
dsim-firmware-unit-test: comp
	mkdir -p $(DSIM_RESULTS)/firmware && cd $(DSIM_RESULTS)/firmware && \
	$(DSIM) -l dsim-$(UNIT_TEST).log -image $(DSIM_IMAGE) \
		-work $(DSIM_WORK) $(DSIM_RUN_FLAGS) $(DSIM_DMP_FLAGS) \
		-sv_lib $(UVM_HOME)/src/dpi/libuvm_dpi.so \
		+UVM_TESTNAME=uvmt_cv32_firmware_test_c \
		+firmware=$(FIRMWARE)/firmware_unit_test.hex

# Aliases for 'dsim-unit-test' (defined in ../Common.mk)
.PHONY: unit-test
unit-test: dsim-unit-test

###############################################################################
# Clean up your mess!

# Metrics dsim cleanup
clean:
	rm -f dsim.log
	rm -f dsim-*.log
	rm -f metrics_history.db
	rm -f metrics.db
	rm -f metrics.xml
	rm -f trace_core_00_0.log
	rm -rf dsim_work
	rm -f dsim.env
	rm -f $(DSIM_IMAGE)
	rm -rf $(DSIM_RESULTS)

# All generated files plus the clone of the RTL
clean_all: clean clean_core_tests clean_riscvdv clean_test_programs
	rm -rf $(CV32E40P_PKG)
