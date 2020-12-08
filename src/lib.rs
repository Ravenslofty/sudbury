mod gpr;
mod i460gx;

use std::convert::TryInto;
use yaxpeax_arch::Decoder;

pub enum Action {
    Continue,
    BranchTaken,
}

/// An IA64 CPU.
pub struct Cpu {
    regs: gpr::Regs,
    rom: Vec<u8>,
    i460gx: i460gx::I460GX,
}

impl Cpu {
    pub fn new(rom: Vec<u8>) -> Self {
        assert_eq!(rom.len(), 4 * 1024 * 1024);

        const SALE_ENTRY_PTR: u64 = 0xFFFF_FFE8;
        let mut ia64 = Self {
            regs: gpr::Regs::new(),
            rom,
            i460gx: i460gx::I460GX::new(),
        };
        let sale_entry = u64::from_le_bytes(ia64.read8(SALE_ENTRY_PTR));
        ia64.regs.write_ip(sale_entry);
        ia64
    }

    pub fn read1(&self, addr: u64) -> u8 {
        let addr = addr & 0xFFFF_FFFF;
        match addr {
            // ROM
            0xFFC0_0000 ..= 0xFFFF_FFFF => {
                let addr = (addr - 0xFFC0_0000) as usize;
                self.rom[addr]
            },
            _ => unimplemented!("unrecognised read1 from 0x{:016x}", addr),
        }
    }

    pub fn read2(&self, addr: u64) -> [u8; 2] {
        let addr = addr & 0xFFFF_FFFF;
        match addr {
            // ROM
            0xFFC0_0000 ..= 0xFFFF_FFFF => {
                let addr = (addr - 0xFFC0_0000) as usize;
                self.rom[addr..addr+2].try_into().unwrap()
            },
            _ => unimplemented!("unrecognised read2 from 0x{:016x}", addr),
        }
    }

    pub fn read4(&self, addr: u64) -> [u8; 4] {
        let addr = addr & 0xFFFF_FFFF;
        match addr {
            // 460GX SAC undocumented register
            0xFEB0_0CB0 => {
                self.i460gx.read_sac_feb00cb0().to_le_bytes()
            },
            // ROM
            0xFFC0_0000 ..= 0xFFFF_FFFF => {
                let addr = (addr - 0xFFC0_0000) as usize;
                self.rom[addr..addr+4].try_into().unwrap()
            },
            _ => unimplemented!("unrecognised read4 from 0x{:016x}", addr),
        } 
    }

    pub fn read8(&self, addr: u64) -> [u8; 8] {
        let addr = addr & 0xFFFF_FFFF;
        match addr {
            // ROM
            0xFFC0_0000 ..= 0xFFFF_FFFF => {
                let addr = (addr - 0xFFC0_0000) as usize;
                self.rom[addr..addr+8].try_into().unwrap()
            },
            _ => unimplemented!("unrecognised read8 from 0x{:016x}", addr),
        }
    }

    pub fn read16(&self, addr: u64) -> [u8; 16] {
        let addr = addr & 0xFFFF_FFFF;
        match addr {
            // ROM
            0xFFC0_0000 ..= 0xFFFF_FFFF => {
                let addr = (addr - 0xFFC0_0000) as usize;
                self.rom[addr..addr+16].try_into().unwrap()
            },
            _ => unimplemented!("unrecognised read16 from 0x{:016x}", addr),
        }
    }

    pub fn step_instruction(&mut self, instruction: &yaxpeax_ia64::Instruction) -> Action {
        use yaxpeax_ia64::{Opcode, Operand};

        let pred = self.regs.read_pr(instruction.predicate().into());

        let read_source = |regs: &gpr::Regs, source: &Operand| -> (u64, bool) {
            match source {
                Operand::BranchRegister(yaxpeax_ia64::BranchRegister(br)) => (regs.read_br(*br as usize), false),
                Operand::ControlRegister(yaxpeax_ia64::ControlRegister(cr)) => (regs.read_cr(*cr as usize).unwrap(), false),
                Operand::FloatRegister(yaxpeax_ia64::FloatRegister(fpr)) => (regs.read_fpr(*fpr as usize).to_bits(), false),
                Operand::GPRegister(yaxpeax_ia64::GPRegister(gpr)) => regs.read_gpr(*gpr as usize),
                Operand::ImmI64(imm) => (*imm as u64, false),
                Operand::ImmU64(imm) => (*imm, false),
                Operand::IP => (regs.read_ip(), false),
                Operand::Memory(yaxpeax_ia64::GPRegister(gpr)) => regs.read_gpr(*gpr as usize),
                Operand::PSR => (regs.read_psr(), false),
                _ => todo!("source: {:?}", source),
            }
        };

        let write_dest = |regs: &mut gpr::Regs, dest: &Operand, reg: u64, nat: bool| {
            match dest {
                Operand::ApplicationRegister(yaxpeax_ia64::ApplicationRegister(index)) => {
                    assert!(!nat);
                    eprintln!("ar{} <= {:016x}", index, reg);
                    regs.write_ar(*index as usize, reg).unwrap();
                }
                Operand::BranchRegister(yaxpeax_ia64::BranchRegister(index)) => {
                    assert!(!nat);
                    eprintln!("b{} <= {:016x}", index, reg);
                    regs.write_br(*index as usize, reg);
                },
                Operand::ControlRegister(yaxpeax_ia64::ControlRegister(index)) => {
                    assert!(!nat);
                    eprintln!("cr{} <= {:016x}", index, reg);
                    regs.write_cr(*index as usize, reg).unwrap();
                },
                Operand::FloatRegister(yaxpeax_ia64::FloatRegister(index)) => {
                    assert!(!nat);
                    eprintln!("f{} <= {:016x}", index, reg);
                    regs.write_fpr(*index as usize, f64::from_bits(reg)).unwrap();
                }
                Operand::GPRegister(yaxpeax_ia64::GPRegister(index)) | Operand::Memory(yaxpeax_ia64::GPRegister(index)) => {
                    eprintln!("r{} <= {:016x} {}", index, reg, if nat { "(NaT)" } else { "" });
                    regs.write_gpr(*index as usize, reg, nat).unwrap();
                },
                Operand::PredicateRegister(yaxpeax_ia64::PredicateRegister(index)) => {
                    assert!(!nat);
                    eprintln!("p{} <= {}", index, reg == 1);
                    regs.write_pr(*index as usize, reg == 1);
                },
                Operand::PSR_l => {
                    assert!(!nat);
                    let psr = regs.read_psr() & 0xFFFF_FFFF_0000_0000;
                    regs.write_psr(psr | (reg & 0xFFFF_FFFF));
                },
                _ => todo!("dest: {:?}", dest),
            }
        };

        match instruction.opcode() {
            Opcode::Addl => {
                if !pred { return Action::Continue; }
                let operands = instruction.operands();
                let (source1, nat1) = read_source(&self.regs, &operands[1]);
                let (source2, nat2) = read_source(&self.regs, &operands[2]);
                let reg = ((source1 as i64) + (source2 as i64)) as u64;
                write_dest(&mut self.regs, &operands[0], reg, nat1 || nat2);
                Action::Continue
            },
            Opcode::Adds => {
                if !pred { return Action::Continue; }
                let operands = instruction.operands();
                let (source1, nat1) = read_source(&self.regs, &operands[1]);
                let (source2, nat2) = read_source(&self.regs, &operands[2]);
                let reg = ((source1 as i64) + (source2 as i64)) as u64;
                write_dest(&mut self.regs, &operands[0], reg, nat1 || nat2);
                Action::Continue
            },
            Opcode::And => {
                if !pred { return Action::Continue; }
                let operands = instruction.operands();
                let (source1, nat1) = read_source(&self.regs, &operands[1]);
                let (source2, nat2) = read_source(&self.regs, &operands[2]);
                write_dest(&mut self.regs, &operands[0], source1 & source2, nat1 || nat2);
                Action::Continue
            },
            Opcode::Br_call => {
                if !pred { return Action::Continue; }
                let target = match instruction.operands()[0] {
                    Operand::ImmI64(imm) => ((self.regs.read_ip() as i64) + imm) as u64,
                    Operand::BranchRegister(yaxpeax_ia64::BranchRegister(br)) => self.regs.read_br(br as usize),
                    _ => todo!("br_call source: {:?}", instruction.operands()[0]),
                };
                let cfm = self.regs.read_cfm();
                let ec = self.regs.read_ar(gpr::AR_EC).unwrap() & 0x3F;
                let cpl = (self.regs.read_psr() & gpr::PSR_CPL) >> 32;
                let pfs = cfm | ec << 52 | cpl << 62;
                let sof = cfm & gpr::CFM_SOF;
                let sol = (cfm & gpr::CFM_SOL) >> 7;
                self.regs.write_ar(gpr::AR_PFS, pfs).unwrap();
                self.regs.write_br(1, self.regs.read_ip() + 16);
                self.regs.write_cfm(sof - sol);
                self.regs.write_ip(target);
                Action::BranchTaken
            }
            Opcode::Br_cond => {
                if !pred { return Action::Continue; }
                let target = match instruction.operands()[0] {
                    Operand::ImmI64(imm) => ((self.regs.read_ip() as i64) + imm) as u64,
                    Operand::BranchRegister(yaxpeax_ia64::BranchRegister(br)) => self.regs.read_br(br as usize),
                    _ => todo!("br_cond source: {:?}", instruction.operands()[0]),
                };
                self.regs.write_ip(target);
                Action::BranchTaken
            },
            Opcode::Break_m => {
                if !pred { return Action::Continue; }
                panic!("Break Instruction");
            },
            Opcode::Bsw_0 => {
                self.regs.bank_switch(0);
                Action::Continue
            },
            Opcode::Bsw_1 => {
                self.regs.bank_switch(1);
                Action::Continue
            },
            Opcode::Clrrb => {
                let cfm = self.regs.read_cfm();
                self.regs.write_cfm(cfm & !gpr::CFM_RRB_FR & !gpr::CFM_RRB_GR & !gpr::CFM_RRB_PR);
                Action::Continue
            },
            Opcode::Cmp_eq => {
                assert!(pred);
                let operands = instruction.operands();
                assert_ne!(operands[0], operands[1], "Illegal Operation");
                let (source1, nat1) = read_source(&self.regs, &operands[2]);
                let (source2, nat2) = read_source(&self.regs, &operands[3]);
                assert!(!nat1);
                assert!(!nat2);
                let eq = source1 == source2;
                write_dest(&mut self.regs, &operands[0], eq as u64, false);
                write_dest(&mut self.regs, &operands[1], !eq as u64, false);
                Action::Continue
            },
            Opcode::Cmp_lt => {
                assert!(pred);
                let operands = instruction.operands();
                assert_ne!(operands[0], operands[1], "Illegal Operation");
                let (source1, nat1) = read_source(&self.regs, &operands[2]);
                let (source2, nat2) = read_source(&self.regs, &operands[3]);
                assert!(!nat1);
                assert!(!nat2);
                let eq = source1 < source2;
                write_dest(&mut self.regs, &operands[0], eq as u64, false);
                write_dest(&mut self.regs, &operands[1], !eq as u64, false);
                Action::Continue
            },
            Opcode::Dep => {
                if !pred { return Action::Continue; }
                let operands = instruction.operands();
                let (source1, nat1) = read_source(&self.regs, &operands[1]);
                let (source2, nat2) = read_source(&self.regs, &operands[2]);
                let pos = read_source(&self.regs, &operands[3]).0;
                let len = read_source(&self.regs, &operands[4]).0;
                let mask = (1 << (len + 1)) - 1;
                let source1 = (source1 & mask) << pos;
                let source2 = source2 & !(mask << pos);
                write_dest(&mut self.regs, &operands[0], source1 | source2, nat1 || nat2);
                Action::Continue
            },
            Opcode::Dep_z => {
                if !pred { return Action::Continue; }
                let operands = instruction.operands();
                let (source1, nat1) = read_source(&self.regs, &operands[1]);
                let pos = read_source(&self.regs, &operands[2]).0;
                let len = read_source(&self.regs, &operands[3]).0;
                let mask = (1 << (len + 1)) - 1;
                let source1 = (source1 & mask) << pos;
                write_dest(&mut self.regs, &operands[0], source1, nat1);
                Action::Continue
            },
            Opcode::Extr => {
                let operands = instruction.operands();
                let (source1, nat1) = read_source(&self.regs, &operands[1]);
                assert!(!nat1);
                let source1 = source1 as i64;
                let pos = read_source(&self.regs, &operands[2]).0 as u32;
                let len = read_source(&self.regs, &operands[3]).0 as u32;
                let mask = (1_i64.wrapping_shl(len + pos + 1)) - 1;
                let source1 = (source1 & mask) >> pos;
                write_dest(&mut self.regs, &operands[0], source1 as u64, nat1);
                Action::Continue
            },
            Opcode::Extr_u => {
                let operands = instruction.operands();
                let (source1, nat1) = read_source(&self.regs, &operands[1]);
                assert!(!nat1);
                let pos = read_source(&self.regs, &operands[2]).0 as u32;
                let len = read_source(&self.regs, &operands[3]).0 as u32;
                let mask = (1_u64.wrapping_shl(len + pos + 1)) - 1;
                let source1 = (source1 & mask) >> pos;
                write_dest(&mut self.regs, &operands[0], source1, nat1);
                Action::Continue
            },
            Opcode::Flushrs => {
                eprintln!("flushrs stubbed");
                Action::Continue
            },
            Opcode::Fmerge_s => {
                if !pred { return Action::Continue; }
                let operands = instruction.operands();
                let (source1, nat1) = read_source(&self.regs, &operands[1]);
                let (source2, nat2) = read_source(&self.regs, &operands[2]);
                assert!(!nat1 && !nat2);
                let source1 = f64::from_bits(source1);
                let source2 = f64::from_bits(source2);
                write_dest(&mut self.regs, &operands[0], source2.copysign(source1).to_bits(), false);
                Action::Continue
            },
            Opcode::Ld1 => {
                if !pred { return Action::Continue; }
                let operands = instruction.operands();
                assert!(operands.len() == 2 || operands.len() == 3);
                let (source, nat) = read_source(&self.regs, &operands[1]);
                assert!(!nat, "Register NaT Consumption");
                let data = u64::from(self.read1(source));
                write_dest(&mut self.regs, &operands[0], data, false);
                if operands.len() == 3 {
                    let offset = read_source(&self.regs, &operands[2]).0;
                    let reg = ((source as i64) + (offset as i64)) as u64;
                    write_dest(&mut self.regs, &operands[1], reg, false);
                }
                Action::Continue
            },
            Opcode::Ld2 => {
                if !pred { return Action::Continue; }
                let operands = instruction.operands();
                assert!(operands.len() == 2 || operands.len() == 3);
                let (source, nat) = read_source(&self.regs, &operands[1]);
                assert!(!nat, "Register NaT Consumption");
                let data = u16::from_le_bytes(self.read2(source)) as u64;
                write_dest(&mut self.regs, &operands[0], data, false);
                if operands.len() == 3 {
                    let offset = read_source(&self.regs, &operands[2]).0;
                    let reg = ((source as i64) + (offset as i64)) as u64;
                    write_dest(&mut self.regs, &operands[1], reg, false);
                }
                Action::Continue
            },
            Opcode::Ld4_acq => {
                if !pred { return Action::Continue; }
                let operands = instruction.operands();
                assert!(operands.len() == 2 || operands.len() == 3);
                let (source, nat) = read_source(&self.regs, &operands[1]);
                assert!(!nat, "Register NaT Consumption");
                let data = u32::from_le_bytes(self.read4(source));
                write_dest(&mut self.regs, &operands[0], data.into(), false);
                if operands.len() == 3 {
                    let offset = read_source(&self.regs, &operands[2]).0;
                    let reg = ((source as i64) + (offset as i64)) as u64;
                    write_dest(&mut self.regs, &operands[1], reg, false);
                }
                Action::Continue
            },
            Opcode::Ld8 => {
                if !pred { return Action::Continue; }
                let operands = instruction.operands();
                assert!(operands.len() == 2 || operands.len() == 3);
                let (source, nat) = read_source(&self.regs, &operands[1]);
                assert!(!nat, "Register NaT Consumption");
                let data = u64::from_le_bytes(self.read8(source));
                write_dest(&mut self.regs, &operands[0], data, false);
                if operands.len() == 3 {
                    let offset = read_source(&self.regs, &operands[2]).0;
                    let reg = ((source as i64) + (offset as i64)) as u64;
                    write_dest(&mut self.regs, &operands[1], reg, false);
                }
                Action::Continue
            },
            Opcode::Mov | Opcode::Movl | Opcode::Mov_m => {
                if !pred { return Action::Continue; }
                let operands = instruction.operands();
                assert_eq!(operands.len(), 2);
                let (source, nat) = read_source(&self.regs, &operands[1]);
                write_dest(&mut self.regs, &operands[0], source, nat);
                Action::Continue
            },
            Opcode::Mov_mwh_ih => {
                if !pred { return Action::Continue; }
                let operands = instruction.operands();
                let (source, nat) = read_source(&self.regs, &operands[1]);
                assert!(!nat, "Register NaT Consumption");
                write_dest(&mut self.regs, &operands[0], source, false);
                Action::Continue
            },
            Opcode::Nop_b | Opcode::Nop_f | Opcode::Nop_i | Opcode::Nop_m | Opcode::Nop_x => Action::Continue,
            Opcode::Rfi => {
                assert!(pred);
                let ipsr = self.regs.read_cr(gpr::CR_IPSR).unwrap();
                let iip = self.regs.read_cr(gpr::CR_IIP).unwrap();
                self.regs.write_psr(ipsr);
                self.regs.write_ip(iip);
                Action::BranchTaken
            },
            Opcode::Rsm => {
                assert!(pred);
                let operands = instruction.operands();
                let source = !(read_source(&self.regs, &operands[0]).0 & 0xFFFFFF);
                let psr = self.regs.read_psr();
                self.regs.write_psr(psr & source);
                Action::Continue
            },
            Opcode::Srlz_i | Opcode::Srlz_d => Action::Continue,
            Opcode::Tbit_z => {
                assert!(pred);
                let operands = instruction.operands();
                assert_ne!(operands[0], operands[1], "Illegal Operation");
                let (source1, nat1) = read_source(&self.regs, &operands[2]);
                let (source2, nat2) = read_source(&self.regs, &operands[3]);
                assert!(!nat1);
                assert!(!nat2);
                let eq = (source1 >> source2) & 1 == 0;
                write_dest(&mut self.regs, &operands[0], eq as u64, false);
                write_dest(&mut self.regs, &operands[1], !eq as u64, false);
                Action::Continue
            },
            _ => todo!("{:?} {0}", instruction),
        }
    }

    pub fn step_bundle(&mut self) {
        let ip = self.regs.read_ip();
        let bytes = self.read16(ip);
        let decoder = yaxpeax_ia64::InstDecoder::default();
        let bundle = decoder.decode(bytes.iter().copied()).unwrap();
        print!("{:016x}: ", ip);
        for byte in &bytes {
            print!("{:02x}", byte);
        }
        println!(" {}", bundle);

        let mut branch_taken = false;
        for instruction in bundle.instructions() {
            match self.step_instruction(instruction) {
                Action::Continue => {},
                Action::BranchTaken => {
                    eprintln!("*** BRANCH ***");
                    branch_taken = true;
                    break;
                }
            }
        }

        if !branch_taken {
            self.regs.write_ip(ip + 16);
        }
    }
}

