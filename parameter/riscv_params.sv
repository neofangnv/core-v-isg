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

// reset pc vector
// NEED_CHANGE
`define RESET_PC    `RISCV_PA_EXTMEM1_START + 'h200

// consider as simulation end when seeing N times of same pc
`define END_LOOP_PC_TIMES   16

// default constraint branch range
`define DEFAULT_BR_RANGE    0

// NEED_CHANGE
`define RISCV_PA_EXTMEM1_START	'h6000_0000_0000_0000

`define RISCV_CSR_MCAUSE_EXCODE_IAMA                       5'h00
`define RISCV_CSR_MCAUSE_EXCODE_IACC_FAULT                 5'h01
`define RISCV_CSR_MCAUSE_EXCODE_ILL                        5'h02
`define RISCV_CSR_MCAUSE_EXCODE_BKPT                       5'h03
`define RISCV_CSR_MCAUSE_EXCODE_LAMA                       5'h04
`define RISCV_CSR_MCAUSE_EXCODE_LACC_FAULT                 5'h05
`define RISCV_CSR_MCAUSE_EXCODE_SAMA                       5'h06
`define RISCV_CSR_MCAUSE_EXCODE_SACC_FAULT                 5'h07
`define RISCV_CSR_MCAUSE_EXCODE_UCALL                      5'h08
`define RISCV_CSR_MCAUSE_EXCODE_SCALL                      5'h09
`define RISCV_CSR_MCAUSE_EXCODE_MCALL                      5'h0b
`define RISCV_CSR_MCAUSE_EXCODE_IPAGE_FAULT                5'h0c
`define RISCV_CSR_MCAUSE_EXCODE_LPAGE_FAULT                5'h0d
`define RISCV_CSR_MCAUSE_EXCODE_SPAGE_FAULT                5'h0f
`define RISCV_CSR_MCAUSE_EXCODE_U_SWINT                    5'h00
`define RISCV_CSR_MCAUSE_EXCODE_S_SWINT                    5'h01
`define RISCV_CSR_MCAUSE_EXCODE_M_SWINT                    5'h03
`define RISCV_CSR_MCAUSE_EXCODE_U_TINT                     5'h04
`define RISCV_CSR_MCAUSE_EXCODE_S_TINT                     5'h05
`define RISCV_CSR_MCAUSE_EXCODE_M_TINT                     5'h07
`define RISCV_CSR_MCAUSE_EXCODE_U_EINT                     5'h08
`define RISCV_CSR_MCAUSE_EXCODE_S_EINT                     5'h09
`define RISCV_CSR_MCAUSE_EXCODE_M_EINT                     5'h0b

`define RISCV_CSR_SCAUSE_EXCODE_IAMA                       5'h00
`define RISCV_CSR_SCAUSE_EXCODE_IACC_FAULT                 5'h01
`define RISCV_CSR_SCAUSE_EXCODE_ILL                        5'h02
`define RISCV_CSR_SCAUSE_EXCODE_BKPT                       5'h03
`define RISCV_CSR_SCAUSE_EXCODE_LAMA                       5'h04
`define RISCV_CSR_SCAUSE_EXCODE_LACC_FAULT                 5'h05
`define RISCV_CSR_SCAUSE_EXCODE_SAMA                       5'h06
`define RISCV_CSR_SCAUSE_EXCODE_SACC_FAULT                 5'h07
`define RISCV_CSR_SCAUSE_EXCODE_UCALL                      5'h08
`define RISCV_CSR_SCAUSE_EXCODE_SCALL                      5'h09
`define RISCV_CSR_SCAUSE_EXCODE_IPAGE_FAULT                5'h0c
`define RISCV_CSR_SCAUSE_EXCODE_LPAGE_FAULT                5'h0d
`define RISCV_CSR_SCAUSE_EXCODE_SPAGE_FAULT                5'h0f
`define RISCV_CSR_SCAUSE_EXCODE_U_SWINT                    5'h00
`define RISCV_CSR_SCAUSE_EXCODE_S_SWINT                    5'h01
`define RISCV_CSR_SCAUSE_EXCODE_U_TINT                     5'h04
`define RISCV_CSR_SCAUSE_EXCODE_S_TINT                     5'h05
`define RISCV_CSR_SCAUSE_EXCODE_U_EINT                     5'h08
`define RISCV_CSR_SCAUSE_EXCODE_S_EINT                     5'h09

`define RISCV_CSR_MSTATUS_UIE                                0:0
`define RISCV_CSR_MSTATUS_SIE                                1:1
`define RISCV_CSR_MSTATUS_WPRI0                              2:2
`define RISCV_CSR_MSTATUS_MIE                                3:3
`define RISCV_CSR_MSTATUS_UPIE                               4:4
`define RISCV_CSR_MSTATUS_SPIE                               5:5
`define RISCV_CSR_MSTATUS_WPRI1                              6:6
`define RISCV_CSR_MSTATUS_MPIE                               7:7
`define RISCV_CSR_MSTATUS_SPP                                8:8
`define RISCV_CSR_MSTATUS_WPRI2                             10:9
`define RISCV_CSR_MSTATUS_MPP                              12:11
`define RISCV_CSR_MSTATUS_FS                               14:13
`define RISCV_CSR_MSTATUS_XS                               16:15
`define RISCV_CSR_MSTATUS_MPRV                             17:17
`define RISCV_CSR_MSTATUS_SUM                              18:18
`define RISCV_CSR_MSTATUS_MXR                              19:19
`define RISCV_CSR_MSTATUS_TVM                              20:20
`define RISCV_CSR_MSTATUS_TW                               21:21
`define RISCV_CSR_MSTATUS_TSR                              22:22
`define RISCV_CSR_MSTATUS_WPRI3                            31:24
`define RISCV_CSR_MSTATUS_UXL                              33:32
`define RISCV_CSR_MSTATUS_SXL                              35:34
`define RISCV_CSR_MSTATUS_WPRI4                            62:36
`define RISCV_CSR_MSTATUS_SD                               63:63

`define RISCV_CSR_MCOUNTEREN_CY                              0:0
`define RISCV_CSR_MCOUNTEREN_TM                              1:1
`define RISCV_CSR_MCOUNTEREN_IR                              2:2
`define RISCV_CSR_MCOUNTEREN_HPM                            31:3
`define RISCV_CSR_MCOUNTEREN_RS0                           63:32

`define RISCV_CSR_SCOUNTEREN_CY                              0:0
`define RISCV_CSR_SCOUNTEREN_TM                              1:1
`define RISCV_CSR_SCOUNTEREN_IR                              2:2
`define RISCV_CSR_SCOUNTEREN_HPM                            31:3
`define RISCV_CSR_SCOUNTEREN_RS0                           63:32

`define RISCV_CSR_MEDELEG_MISALIGNED_FETCH                   0:0
`define RISCV_CSR_MEDELEG_FAULT_FETCH                        1:1
`define RISCV_CSR_MEDELEG_ILLEGAL_INSTRUCTION                2:2
`define RISCV_CSR_MEDELEG_BREAKPOINT                         3:3
`define RISCV_CSR_MEDELEG_MISALIGNED_LOAD                    4:4
`define RISCV_CSR_MEDELEG_FAULT_LOAD                         5:5
`define RISCV_CSR_MEDELEG_MISALIGNED_STORE                   6:6
`define RISCV_CSR_MEDELEG_FAULT_STORE                        7:7
`define RISCV_CSR_MEDELEG_USER_ECALL                         8:8
`define RISCV_CSR_MEDELEG_WPRI0                             11:9
`define RISCV_CSR_MEDELEG_FETCH_PAGE_FAULT                 12:12
`define RISCV_CSR_MEDELEG_LOAD_PAGE_FAULT                  13:13
`define RISCV_CSR_MEDELEG_WPRI1                            14:14
`define RISCV_CSR_MEDELEG_STORE_PAGE_FAULT                 15:15
`define RISCV_CSR_MEDELEG_WPRI2                            27:16
`define RISCV_CSR_MEDELEG_USS                              28:28
`define RISCV_CSR_MEDELEG_WPRI3                            63:29

`define RISCV_CSR_MIDELEG_USID                               0:0
`define RISCV_CSR_MIDELEG_SSID                               1:1
`define RISCV_CSR_MIDELEG_WPRI0                              3:2
`define RISCV_CSR_MIDELEG_UTID                               4:4
`define RISCV_CSR_MIDELEG_STID                               5:5
`define RISCV_CSR_MIDELEG_WPRI1                              7:6
`define RISCV_CSR_MIDELEG_UEID                               8:8
`define RISCV_CSR_MIDELEG_SEID                               9:9
`define RISCV_CSR_MIDELEG_WPRI2                            63:10

`define RISCV_CSR_MTVEC_MODE                                 1:0
`define RISCV_CSR_MTVEC_BASE                                63:2

`define RISCV_CSR_STVEC_MODE                                 1:0
`define RISCV_CSR_STVEC_BASE                                63:2

`define RISCV_CSR_MIE_USIE                                   0:0
`define RISCV_CSR_MIE_SSIE                                   1:1
`define RISCV_CSR_MIE_WPRI0                                  2:2
`define RISCV_CSR_MIE_MSIE                                   3:3
`define RISCV_CSR_MIE_UTIE                                   4:4
`define RISCV_CSR_MIE_STIE                                   5:5
`define RISCV_CSR_MIE_WPRI1                                  6:6
`define RISCV_CSR_MIE_MTIE                                   7:7
`define RISCV_CSR_MIE_UEIE                                   8:8
`define RISCV_CSR_MIE_SEIE                                   9:9
`define RISCV_CSR_MIE_WPRI2                                10:10
`define RISCV_CSR_MIE_MEIE                                 11:11
`define RISCV_CSR_MIE_WPRI3                                63:12



// NEED_CHANGE
// Machine mode CSR register address
`define CSR_MVENDORID		(`RISCV_CSR_MVENDORID >> 2)
`define CSR_MARCHID			(`RISCV_CSR_MARCHID >> 2)
`define CSR_MIMPID			(`RISCV_CSR_MIMPID >> 2)
`define CSR_MHARTID			(`RISCV_CSR_MHARTID >> 2)

`define CSR_MSTATUS         (`RISCV_CSR_MSTATUS >> 2)
`define CSR_MISA			(`RISCV_CSR_MISA >> 2)
`define CSR_MEDELEG         (`RISCV_CSR_MEDELEG >> 2)
`define CSR_MIDELEG         (`RISCV_CSR_MIDELEG >> 2)
`define CSR_MIE             (`RISCV_CSR_MIE >> 2)
`define CSR_MTVEC           (`RISCV_CSR_MTVEC >> 2)
`define CSR_MCOUNTEREN		(`RISCV_CSR_MCOUNTEREN >> 2)

`define CSR_MHPMEVENT3      (`RISCV_CSR_MHPMEVENT3 >> 2)
`define CSR_MHPMEVENT4      (`RISCV_CSR_MHPMEVENT4 >> 2)
`define CSR_MHPMEVENT5      (`RISCV_CSR_MHPMEVENT5 >> 2) 
`define CSR_MHPMEVENT6      (`RISCV_CSR_MHPMEVENT6 >> 2) 
`define CSR_MHPMEVENT7      (`RISCV_CSR_MHPMEVENT7 >> 2) 
`define CSR_MHPMEVENT8      (`RISCV_CSR_MHPMEVENT8 >> 2) 
`define CSR_MHPMEVENT9      (`RISCV_CSR_MHPMEVENT9 >> 2) 
`define CSR_MHPMEVENT10     (`RISCV_CSR_MHPMEVENT10 >> 2)
`define CSR_MHPMEVENT31     (`RISCV_CSR_MHPMEVENT31 >> 2)

`define CSR_MSCRATCH		(`RISCV_CSR_MSCRATCH >> 2)
`define CSR_MEPC            (`RISCV_CSR_MEPC >> 2)
`define CSR_MCAUSE			(`RISCV_CSR_MCAUSE >> 2)
`define CSR_MTVAL			(`RISCV_CSR_MTVAL >> 2)
`define CSR_MIP				(`RISCV_CSR_MIP >> 2)

`define CSR_PMPCFG0         (`RISCV_CSR_PMPCFG0 >> 2)
`define CSR_PMPCFG2         (`RISCV_CSR_PMPCFG2 >> 2)
`define CSR_PMPADDR0        (`RISCV_CSR_PMPADDR0 >> 2)
`define CSR_PMPADDR1        (`RISCV_CSR_PMPADDR1 >> 2)  
`define CSR_PMPADDR2        (`RISCV_CSR_PMPADDR2 >> 2)  
`define CSR_PMPADDR3        (`RISCV_CSR_PMPADDR3 >> 2)  
`define CSR_PMPADDR4        (`RISCV_CSR_PMPADDR4 >> 2)  
`define CSR_PMPADDR5        (`RISCV_CSR_PMPADDR5 >> 2)  
`define CSR_PMPADDR6        (`RISCV_CSR_PMPADDR6 >> 2)  
`define CSR_PMPADDR7        (`RISCV_CSR_PMPADDR7 >> 2)  
`define CSR_PMPADDR8        (`RISCV_CSR_PMPADDR8 >> 2)  
`define CSR_PMPADDR9        (`RISCV_CSR_PMPADDR9 >> 2)  
`define CSR_PMPADDR10       (`RISCV_CSR_PMPADDR10 >> 2)  
`define CSR_PMPADDR11       (`RISCV_CSR_PMPADDR11 >> 2)  
`define CSR_PMPADDR12       (`RISCV_CSR_PMPADDR12 >> 2)  
`define CSR_PMPADDR13       (`RISCV_CSR_PMPADDR13 >> 2)  
`define CSR_PMPADDR14       (`RISCV_CSR_PMPADDR14 >> 2)  
`define CSR_PMPADDR15       (`RISCV_CSR_PMPADDR15 >> 2)  


`define CSR_MCYCLE			(`RISCV_CSR_MHPMCOUNTER_MCYCLE >> 2)
`define CSR_MINSTRET		(`RISCV_CSR_MHPMCOUNTER_MINSTRET >> 2)
`define CSR_MHPMCOUNTER0    (`RISCV_CSR_MHPMCOUNTER0 >> 2)
`define CSR_MHPMCOUNTER1    (`RISCV_CSR_MHPMCOUNTER1 >> 2)
`define CSR_MHPMCOUNTER2    (`RISCV_CSR_MHPMCOUNTER2 >> 2)
`define CSR_MHPMCOUNTER3    (`RISCV_CSR_MHPMCOUNTER3 >> 2)
`define CSR_MHPMCOUNTER4    (`RISCV_CSR_MHPMCOUNTER4 >> 2)
`define CSR_MHPMCOUNTER5    (`RISCV_CSR_MHPMCOUNTER5 >> 2)
`define CSR_MHPMCOUNTER6    (`RISCV_CSR_MHPMCOUNTER6 >> 2)
`define CSR_MHPMCOUNTER7    (`RISCV_CSR_MHPMCOUNTER7 >> 2)
`define CSR_MHPMCOUNTER8    (`RISCV_CSR_MHPMCOUNTER8 >> 2)
`define CSR_MHPMCOUNTER9    (`RISCV_CSR_MHPMCOUNTER9 >> 2)
`define CSR_MHPMCOUNTER10   (`RISCV_CSR_MHPMCOUNTER10>> 2)
`define CSR_MHPMCOUNTER11   (`RISCV_CSR_MHPMCOUNTER11>> 2)
`define CSR_MHPMCOUNTER12   (`RISCV_CSR_MHPMCOUNTER12>> 2)
`define CSR_MHPMCOUNTER13   (`RISCV_CSR_MHPMCOUNTER13>> 2)
`define CSR_MHPMCOUNTER14   (`RISCV_CSR_MHPMCOUNTER14>> 2)
`define CSR_MHPMCOUNTER15   (`RISCV_CSR_MHPMCOUNTER15>> 2)
`define CSR_MHPMCOUNTER16   (`RISCV_CSR_MHPMCOUNTER16>> 2)
`define CSR_MHPMCOUNTER17   (`RISCV_CSR_MHPMCOUNTER17>> 2)
`define CSR_MHPMCOUNTER18   (`RISCV_CSR_MHPMCOUNTER18>> 2)
`define CSR_MHPMCOUNTER19   (`RISCV_CSR_MHPMCOUNTER19>> 2)
`define CSR_MHPMCOUNTER20   (`RISCV_CSR_MHPMCOUNTER20>> 2)
`define CSR_MHPMCOUNTER21   (`RISCV_CSR_MHPMCOUNTER21>> 2)
`define CSR_MHPMCOUNTER22   (`RISCV_CSR_MHPMCOUNTER22>> 2)
`define CSR_MHPMCOUNTER23   (`RISCV_CSR_MHPMCOUNTER23>> 2)
`define CSR_MHPMCOUNTER24   (`RISCV_CSR_MHPMCOUNTER24>> 2)
`define CSR_MHPMCOUNTER25   (`RISCV_CSR_MHPMCOUNTER25>> 2)
`define CSR_MHPMCOUNTER26   (`RISCV_CSR_MHPMCOUNTER26>> 2)
`define CSR_MHPMCOUNTER27   (`RISCV_CSR_MHPMCOUNTER27>> 2)
`define CSR_MHPMCOUNTER28   (`RISCV_CSR_MHPMCOUNTER28>> 2)
`define CSR_MHPMCOUNTER29   (`RISCV_CSR_MHPMCOUNTER29>> 2)
`define CSR_MHPMCOUNTER30   (`RISCV_CSR_MHPMCOUNTER30>> 2)
`define CSR_MHPMCOUNTER31   (`RISCV_CSR_MHPMCOUNTER31 >> 2)

`define CSR_MTIMECMP        (`RISCV_CSR_MTIMECMP >> 2)

// Supervisor mode CSR
`define CSR_SSTATUS         (`RISCV_CSR_SSTATUS >> 2)
`define CSR_SIE             (`RISCV_CSR_SIE >> 2)
`define CSR_STVEC           (`RISCV_CSR_STVEC >> 2)
`define CSR_SCOUNTEREN      (`RISCV_CSR_SCOUNTEREN >> 2)
`define CSR_SSCRATCH        (`RISCV_CSR_SSCRATCH >> 2)
`define CSR_SEPC            (`RISCV_CSR_SEPC >> 2)
`define CSR_SCAUSE          (`RISCV_CSR_SCAUSE >> 2)
`define CSR_STVAL           (`RISCV_CSR_STVAL >> 2)
`define CSR_SIP             (`RISCV_CSR_SIP >> 2)

`define CSR_SATP            (`RISCV_CSR_SATP >> 2)


// User mode CSR
`define CSR_FFLAGS          (`RISCV_CSR_FFLAGS >> 2)
`define CSR_FRM             (`RISCV_CSR_FRM >> 2)
`define CSR_FCSR            (`RISCV_CSR_FCSR >> 2)

`define CSR_CYCLE			(`RISCV_CSR_HPMCOUNTER_CYCLE >> 2)
`define CSR_TIME			(`RISCV_CSR_HPMCOUNTER_TIME >> 2)
`define CSR_INSTRET			(`RISCV_CSR_HPMCOUNTER_INSTRET >> 2)
`define CSR_HPMCOUNTER3     (`RISCV_CSR_HPMCOUNTER3 >> 2)
`define CSR_HPMCOUNTER4     (`RISCV_CSR_HPMCOUNTER4 >> 2)
`define CSR_HPMCOUNTER5     (`RISCV_CSR_HPMCOUNTER5 >> 2)
`define CSR_HPMCOUNTER6     (`RISCV_CSR_HPMCOUNTER6 >> 2)
`define CSR_HPMCOUNTER7     (`RISCV_CSR_HPMCOUNTER7 >> 2)
`define CSR_HPMCOUNTER8     (`RISCV_CSR_HPMCOUNTER8 >> 2)
`define CSR_HPMCOUNTER9     (`RISCV_CSR_HPMCOUNTER9 >> 2)
`define CSR_HPMCOUNTER10    (`RISCV_CSR_HPMCOUNTER10 >> 2)
`define CSR_HPMCOUNTER11    (`RISCV_CSR_HPMCOUNTER11 >> 2)
`define CSR_HPMCOUNTER12    (`RISCV_CSR_HPMCOUNTER12 >> 2)
`define CSR_HPMCOUNTER13    (`RISCV_CSR_HPMCOUNTER13 >> 2)
`define CSR_HPMCOUNTER14    (`RISCV_CSR_HPMCOUNTER14 >> 2)
`define CSR_HPMCOUNTER15    (`RISCV_CSR_HPMCOUNTER15 >> 2)
`define CSR_HPMCOUNTER16    (`RISCV_CSR_HPMCOUNTER16 >> 2)
`define CSR_HPMCOUNTER17    (`RISCV_CSR_HPMCOUNTER17 >> 2)
`define CSR_HPMCOUNTER18    (`RISCV_CSR_HPMCOUNTER18 >> 2)
`define CSR_HPMCOUNTER19    (`RISCV_CSR_HPMCOUNTER19 >> 2)
`define CSR_HPMCOUNTER20    (`RISCV_CSR_HPMCOUNTER20 >> 2)
`define CSR_HPMCOUNTER21    (`RISCV_CSR_HPMCOUNTER21 >> 2)
`define CSR_HPMCOUNTER22    (`RISCV_CSR_HPMCOUNTER22 >> 2)
`define CSR_HPMCOUNTER23    (`RISCV_CSR_HPMCOUNTER23 >> 2)
`define CSR_HPMCOUNTER24    (`RISCV_CSR_HPMCOUNTER24 >> 2)
`define CSR_HPMCOUNTER25    (`RISCV_CSR_HPMCOUNTER25 >> 2)
`define CSR_HPMCOUNTER26    (`RISCV_CSR_HPMCOUNTER26 >> 2)
`define CSR_HPMCOUNTER27    (`RISCV_CSR_HPMCOUNTER27 >> 2)
`define CSR_HPMCOUNTER28    (`RISCV_CSR_HPMCOUNTER28 >> 2)
`define CSR_HPMCOUNTER29    (`RISCV_CSR_HPMCOUNTER29 >> 2)
`define CSR_HPMCOUNTER30    (`RISCV_CSR_HPMCOUNTER30 >> 2)
`define CSR_HPMCOUNTER31    (`RISCV_CSR_HPMCOUNTER31 >> 2)


`define MAX_PMP_NUM         32 
`define BROM_USED_PMP       0
`define MAX_PMP_ADDR_NUM    32
`define MAX_PMP_CFG_NUM     4

`define PMP_OFF             `RISCV_CSR_PMPCFG0_PMP7A_OFF     
`define PMP_TOR             `RISCV_CSR_PMPCFG0_PMP7A_TOR     
`define PMP_NA4             `RISCV_CSR_PMPCFG0_PMP7A_NA4     
`define PMP_NAPOT           `RISCV_CSR_PMPCFG0_PMP7A_NAPOT   
