use std::cell::Cell;

use bitflags::bitflags;
use yaxpeax_arch::{Decoder, U8Reader};
use yaxpeax_ia64::{ApplicationRegister, BranchRegister, DecodeError, GPRegister, IndirectionReg, InstDecoder, InstructionBundle, Opcode, Operand, PredicateRegister};

use crate::{action::Action, mmio::Mmio};

bitflags! {
    struct Psr: u64 {
        const BE  = 1 << 1;
        const UP  = 1 << 2;
        const AC  = 1 << 3;
        const MFL = 1 << 4;
        const MFH = 1 << 5;
        const IC  = 1 << 13;
        const I   = 1 << 14;
        const PK  = 1 << 15;
        const DT  = 1 << 17;
        const DFL = 1 << 18;
        const DFH = 1 << 19;
        const SP  = 1 << 20;
        const PP  = 1 << 21;
        const DI  = 1 << 22;
        const SI  = 1 << 23;
    }
}

pub struct Merced {
    gpr: [Cell<Option<u64>>; 128],
    ar: [Cell<u64>; 128],
    br: [Cell<u64>; 8],
    pr: [Cell<bool>; 64],
    cpuid: [Cell<u64>; 5],
    msr: [Cell<u64>; 2048],
    psr: Cell<Psr>,
    ip: Cell<u64>,
}

impl Merced {
    pub fn new() -> Self {
        // const is needed to copy the cell to initialise gpr.
        #[allow(clippy::declare_interior_mutable_const, dead_code)]
        const CELL_SOME_ZERO: Cell<Option<u64>> = Cell::new(Some(0));
        #[allow(clippy::declare_interior_mutable_const, dead_code)]
        const CELL_ZERO: Cell<u64> = Cell::new(0);
        #[allow(clippy::declare_interior_mutable_const, dead_code)]
        const CELL_FALSE: Cell<bool> = Cell::new(false);

        Self {
            gpr: [CELL_SOME_ZERO; 128],
            ar: [CELL_ZERO; 128],
            br: [CELL_ZERO; 8],
            pr: [CELL_FALSE; 64],
            cpuid: [CELL_ZERO; 5],
            msr: [CELL_ZERO; 2048],
            psr: Cell::new(Psr::empty()),
            ip: CELL_ZERO,
        }
    }

    pub fn reset_exception(&mut self) {
        const PALE_RESET: u64 = 0xFFFF_FFB0;

        // PR0 is always one for unconditional execution.
        self.pr[0].set(true);

        // Minimum number of CPUID registers must be 4 (zero-indexed).
        self.cpuid[0].set(4);

        self.ip.set(PALE_RESET);
    }

    fn build_cmp(&self, predicate: usize, operands: &[Operand], cmp: Box<dyn Fn(i64, i64) -> bool>) -> Box<dyn Fn() -> Action + '_> {
        let dest1 = operands[0];
        let dest2 = operands[1];
        let src1 = operands[2];
        let src2 = operands[3];

        if let Operand::PredicateRegister(PredicateRegister(dest1)) = dest1 {
            if let Operand::PredicateRegister(PredicateRegister(dest2)) = dest2 {
                if let Operand::ImmI64(src1) = src1 {
                    if let Operand::GPRegister(GPRegister(src2)) = src2 {
                        let f: Box<dyn Fn() -> Action> = Box::new(move || {
                            let (result1, result2) = if let Some(src2) = self.gpr[src2 as usize].get() {
                                let cmp = cmp(src1, src2 as i64);
                                (cmp, !cmp)
                            } else {
                                (false, false)
                            };
                            if self.pr[predicate].get() {
                                if dest1 != 0 {
                                    self.pr[dest1 as usize].set(result1);
                                }
                                if dest2 != 0 {
                                    self.pr[dest2 as usize].set(result2);
                                }
                            }
                            Action::Continue
                        });
                        return f;
                    }
                } else if let Operand::GPRegister(GPRegister(src1)) = src1 {
                    if let Operand::GPRegister(GPRegister(src2)) = src2 {
                        let f: Box<dyn Fn() -> Action> = Box::new(move || {
                            let (result1, result2) = if let Some(src1) = self.gpr[src1 as usize].get() {
                                if let Some(src2) = self.gpr[src2 as usize].get() {
                                    let cmp = cmp(src1 as i64, src2 as i64);
                                    (cmp, !cmp)
                                } else {
                                    (false, false)
                                }
                            } else {
                                (false, false)
                            };

                            if self.pr[predicate].get() {
                                if dest1 != 0 {
                                    self.pr[dest1 as usize].set(result1);
                                }
                                if dest2 != 0 {
                                    self.pr[dest2 as usize].set(result2);
                                }
                            }
                            Action::Continue
                        });
                        return f;
                    }
                }
            }
        }

        todo!("build_cmp: {:?}", operands);
    }

    pub fn build_trace<MMIO: Mmio>(&self, mut ip: u64, mmio: &mut MMIO) -> Result<Vec<Box<dyn Fn() -> Action + '_>>, DecodeError> {
        let ia64 = InstDecoder::default();
        let mut bundle = InstructionBundle::default();

        let mut trace = Vec::new();

        println!("*** BEGIN TRACE AT {:016x} ***", ip);
        let mut continue_decoding = true;
        while continue_decoding {
            let insn = mmio.read16(ip).to_le_bytes();
            ia64.decode_into(&mut bundle, &mut U8Reader::new(&insn))?;

            for byte in &insn {
                print!("{:02x} ", byte)
            }
            println!(": {}", bundle);

            for insn in bundle.instructions() {
                let operands = insn.operands();
                match insn.opcode() {
                    Opcode::Addl => {
                        let dest = operands[0];
                        let src1 = operands[1];
                        let src2 = operands[2];

                        if let Operand::GPRegister(GPRegister(dest)) = dest {
                            if let Operand::ImmI64(src1) = src1 {
                                if let Operand::GPRegister(GPRegister(src2)) = src2 {
                                    let predicate = insn.predicate() as usize;
                                    let f: Box<dyn Fn() -> Action> = Box::new(move || {
                                        let result = self.gpr[src2 as usize].get().map(|src2| (src1 + (src2 as i64)) as u64);
                                        if self.pr[predicate].get() {
                                            self.gpr[dest as usize].set(result);
                                        }
                                        Action::Continue
                                    });
                                    trace.push(f);
                                } else {
                                    todo!("{} ({:?})", insn, insn);
                                }
                            } else {
                                todo!("{} ({:?})", insn, insn);
                            }
                        } else {
                            todo!("{} ({:?})", insn, insn);
                        }
                    }
                    Opcode::Br_cond => {
                        let offset = operands[0];

                        if let Operand::ImmI64(imm) = offset {
                            // IP-relative branch.
                            let predicate = insn.predicate() as usize;
                            let f = Box::new(move || {
                                if self.pr[predicate].get() {
                                    let ip = ((ip as i64) + imm) as u64;
                                    self.ip.set(ip);
                                    println!("*** BRANCH TO {:016x} ***", ip);
                                    Action::BranchTaken
                                } else {
                                    self.ip.set(ip);
                                    Action::Continue
                                }
                            });
                            trace.push(f);
                        } else {
                            todo!("{} ({:?})", insn, insn);
                        }

                        continue_decoding = false;
                    },
                    Opcode::Cmp_eq => {
                        trace.push(self.build_cmp(insn.predicate().into(), operands, Box::new(|src1, src2| src1 == src2)));
                    },
                    Opcode::Cmp_lt => {
                        trace.push(self.build_cmp(insn.predicate().into(), operands, Box::new(|src1, src2| src1 < src2)));
                    },
                    Opcode::Dep => {
                        let dest = operands[0];
                        let src1 = operands[1];
                        let src2 = operands[2];
                        let pos = operands[3];
                        let len = operands[4];

                        if let Operand::GPRegister(GPRegister(dest)) = dest {
                            if let Operand::GPRegister(GPRegister(src1)) = src1 {
                                if let Operand::GPRegister(GPRegister(src2)) = src2 {
                                    if let Operand::ImmU64(pos) = pos {
                                        if let Operand::ImmU64(len) = len {
                                            let predicate = insn.predicate() as usize;
                                            let mask = (1 << (len + 1)) - 1;
                                            let f = Box::new(move || {
                                                let result = match (self.gpr[src1 as usize].get(), self.gpr[src2 as usize].get()) {
                                                    (Some(src1), Some(src2)) => {
                                                        let src1 = (src1 & mask) << pos;
                                                        let src2 = (src2 & !mask) << pos;
                                                        Some(src1 | src2)
                                                    },
                                                    (_, _) => None,
                                                };
                                                if self.pr[predicate].get() {
                                                    self.gpr[dest as usize].set(result);
                                                }
                                                Action::Continue
                                            });
                                            trace.push(f);
                                        } else {
                                            todo!("{} ({:?})", insn, insn);
                                        }
                                    } else {
                                        todo!("{} ({:?})", insn, insn);
                                    }
                                } else {
                                    todo!("{} ({:?})", insn, insn);
                                }
                            } else if let Operand::ImmU64(src1) = src1 {
                                if let Operand::GPRegister(GPRegister(src2)) = src2 {
                                    if let Operand::ImmU64(pos) = pos {
                                        if let Operand::ImmU64(len) = len {
                                            let predicate = insn.predicate() as usize;
                                            let mask = (1 << (len + 1)) - 1;
                                            let f = Box::new(move || {
                                                let result = match (self.gpr[src1 as usize].get(), self.gpr[src2 as usize].get()) {
                                                    (Some(src1), Some(src2)) => {
                                                        let src1 = (src1 & mask) << pos;
                                                        let src2 = (src2 & !mask) << pos;
                                                        Some(src1 | src2)
                                                    },
                                                    (_, _) => None,
                                                };
                                                if self.pr[predicate].get() {
                                                    self.gpr[dest as usize].set(result);
                                                }
                                                Action::Continue
                                            });
                                            trace.push(f);
                                        } else {
                                            todo!("{} ({:?})", insn, insn);
                                        }
                                    } else {
                                        todo!("{} ({:?})", insn, insn);
                                    }
                                } else {
                                    todo!("{} ({:?})", insn, insn);
                                }
                            } else {
                                todo!("{} ({:?})", insn, insn);
                            }
                        } else {
                            todo!("{} ({:?})", insn, insn);
                        }
                    },
                    Opcode::Extr_u => {
                        let dest = operands[0];
                        let src = operands[1];
                        let pos = operands[2];
                        let len = operands[3];

                        if let Operand::GPRegister(GPRegister(dest)) = dest {
                            if let Operand::GPRegister(GPRegister(src)) = src {
                                if let Operand::ImmU64(pos) = pos {
                                    if let Operand::ImmU64(len) = len {
                                        let predicate = insn.predicate() as usize;
                                        let mask = (1_u64.wrapping_shl(len as u32 + pos as u32 + 1)) - 1;
                                        let f = Box::new(move || {
                                            if self.pr[predicate].get() {
                                                self.gpr[dest as usize].set(self.gpr[src as usize].get().map(|src| (src & mask) >> pos));
                                            }
                                            Action::Continue
                                        });
                                        trace.push(f);
                                    } else {
                                        todo!("{} ({:?})", insn, insn);
                                    }
                                } else {
                                    todo!("{} ({:?})", insn, insn);
                                }
                            } else {
                                todo!("{} ({:?})", insn, insn);
                            }
                        } else {
                            todo!("{} ({:?})", insn, insn);
                        }
                    }
                    Opcode::Mov => {
                        let operands = insn.operands();
                        let dest = operands[0];
                        let src = operands[1];

                        let predicate = insn.predicate() as usize;

                        if let Operand::GPRegister(GPRegister(gpr)) = dest {
                            if let Operand::ImmI64(imm) = src {
                                let f = Box::new(move || {
                                    if self.pr[predicate].get() {
                                        self.gpr[gpr as usize].set(Some(imm as u64));
                                    }
                                    Action::Continue
                                });
                                trace.push(f);
                            } else if let Operand::GPRegister(GPRegister(src)) = src {
                                let f = Box::new(move || {
                                    if self.pr[predicate].get() {
                                        self.gpr[gpr as usize].set(self.gpr[src as usize].get());
                                    }
                                    Action::Continue
                                });
                                trace.push(f);
                            } else if let Operand::BranchRegister(BranchRegister(src)) = src {
                                let f = Box::new(move || {
                                    if self.pr[predicate].get() {
                                        self.gpr[gpr as usize].set(Some(self.br[src as usize].get()));
                                    }
                                    Action::Continue
                                });
                                trace.push(f);
                            } else if let Operand::IP = src {
                                let f = Box::new(move || {
                                    if self.pr[predicate].get() {
                                        self.gpr[gpr as usize].set(Some(ip));
                                    }
                                    Action::Continue
                                });
                                trace.push(f);
                            } else if let Operand::Indirection(IndirectionReg::Cpuid, GPRegister(src)) = src {
                                let f = Box::new(move || {
                                    if self.pr[predicate].get() {
                                        let src = self.gpr[src as usize].get().expect("NaT consumption");
                                        self.gpr[gpr as usize].set(Some(self.cpuid[src as usize].get()));
                                    }
                                    Action::Continue
                                });
                                trace.push(f);
                            } else if let Operand::Indirection(IndirectionReg::Msr, GPRegister(src)) = src {
                                let f = Box::new(move || {
                                    if self.pr[predicate].get() {
                                        let src = self.gpr[src as usize].get().expect("NaT consumption");
                                        self.gpr[gpr as usize].set(Some(self.msr[src as usize].get()));
                                    }
                                    Action::Continue
                                });
                                trace.push(f);
                            } else {
                                todo!("{} ({:?})", insn, insn);
                            }
                        } else if let Operand::Indirection(IndirectionReg::Msr, GPRegister(dest)) = dest {
                            if let Operand::GPRegister(GPRegister(src)) = src {
                                let f = Box::new(move || {
                                    if self.pr[predicate].get() {
                                        let dest = self.gpr[dest as usize].get().expect("NaT consumption");
                                        self.msr[dest as usize].set(self.gpr[src as usize].get().expect("NaT consumption"));
                                    }
                                    Action::Continue
                                });
                                trace.push(f);
                            }
                        } else {
                            todo!("{} ({:?})", insn, insn);
                        }
                    },
                    Opcode::Mov_m => {
                        let dest = operands[0];
                        let src = operands[1];

                        let predicate = insn.predicate() as usize;

                        if let Operand::ApplicationRegister(ApplicationRegister(dest)) = dest {
                            if let Operand::GPRegister(GPRegister(src)) = src {
                                let f = Box::new(move || {
                                    if self.pr[predicate].get() {
                                        self.ar[dest as usize].set(self.gpr[src as usize].get().expect("NaT consumption"));
                                    }
                                    Action::Continue
                                });
                                trace.push(f);
                            } else {
                                todo!("{} ({:?})", insn, insn);
                            }
                        } else if let Operand::GPRegister(GPRegister(dest)) = dest {
                            if let Operand::ApplicationRegister(ApplicationRegister(src)) = src {
                                let f = Box::new(move || {
                                    if self.pr[predicate].get() {
                                        self.gpr[dest as usize].set(Some(self.ar[src as usize].get()));
                                    }
                                    Action::Continue
                                });
                                trace.push(f);
                            }
                        } else {
                            todo!("{} ({:?})", insn, insn);
                        }
                    },
                    Opcode::Mov_mwh_ih => {
                        let dest = operands[0];
                        let src = operands[1];

                        let predicate = insn.predicate() as usize;

                        if let Operand::BranchRegister(BranchRegister(dest)) = dest {
                            if let Operand::GPRegister(GPRegister(src)) = src {
                                let f = Box::new(move || {
                                    if self.pr[predicate].get() {
                                        self.br[dest as usize].set(self.gpr[src as usize].get().expect("NaT consumption"));
                                    }
                                    Action::Continue
                                });
                                trace.push(f);
                            } else {
                                todo!("{} ({:?})", insn, insn);
                            }
                        }
                    },
                    Opcode::Movl => {
                        let dest = operands[0];
                        let src = operands[1];

                        let predicate = insn.predicate() as usize;

                        if let Operand::GPRegister(GPRegister(dest)) = dest {
                            if let Operand::ImmU64(src) = src {
                                let f = Box::new(move || {
                                    if self.pr[predicate].get() {
                                        self.gpr[dest as usize].set(Some(src));
                                    }
                                    Action::Continue
                                });
                                trace.push(f);
                            } else {
                                todo!("{} ({:?})", insn, insn);
                            }
                        }
                    },
                    Opcode::Rsm => {
                        let mask = operands[0];
                        let predicate = insn.predicate() as usize;

                        if let Operand::ImmU64(mask) = mask {
                            let mask = Psr::from_bits_truncate(!mask);
                            let f = Box::new(move || {
                                if self.pr[predicate].get() {
                                    self.psr.set(self.psr.get() & mask);
                                }
                                Action::Continue
                            });
                            trace.push(f);
                        }
                    },
                    Opcode::Tbit_z => {
                        let dest1 = operands[0];
                        let dest2 = operands[1];
                        let src = operands[2];
                        let pos = operands[3];
                        let predicate = insn.predicate() as usize;

                        if let Operand::GPRegister(GPRegister(src)) = src {
                            if let Operand::ImmU64(pos) = pos {
                                let f = Box::new(move || {
                                    if self.pr[predicate].get() {
                                        let (result1, result2) = if let Some()
                                    }
                                });
                            }
                        }
                    },
                    Opcode::Nop_m | Opcode::Nop_i | Opcode::Nop_f | Opcode::Srlz_i | Opcode::Srlz_d => {},
                    _ => todo!("{} ({:?})", insn, insn),
                }
            }

            ip += 16;
        }
        println!("*** END TRACE AT {:016x} ***", ip);

        Ok(trace)
    }

    pub fn ip(&self) -> u64 {
        self.ip.get()
    }
}

