mod gpr;

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
}

impl Cpu {
    pub fn new(rom: Vec<u8>) -> Self {
        assert_eq!(rom.len(), 4 * 1024 * 1024);

        const SALE_ENTRY_PTR: u64 = 0xFFFF_FFE8;
        let mut ia64 = Self {
            regs: gpr::Regs::new(),
            rom
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
            _ => unimplemented!(),
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
            _ => unimplemented!(),
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
            _ => unimplemented!(),
        }
    }

    pub fn step_instruction(&mut self, instruction: &yaxpeax_ia64::Instruction) -> Action {
        use yaxpeax_ia64::{Opcode, Operand};

        let pred = self.regs.read_pr(instruction.predicate().into());

        let read_source = |regs: &gpr::Regs, source: &Operand| -> (u64, bool) {
            match source {
                Operand::BranchRegister(yaxpeax_ia64::BranchRegister(br)) => (regs.read_br(*br as usize), false),
                Operand::GPRegister(yaxpeax_ia64::GPRegister(gpr)) => regs.read_gpr(*gpr as usize),
                Operand::ImmI64(imm) => (*imm as u64, false),
                Operand::ImmU64(imm) => (*imm, false),
                Operand::IP => (regs.read_ip(), false),
                Operand::Memory(yaxpeax_ia64::GPRegister(gpr)) => regs.read_gpr(*gpr as usize),
                _ => todo!("source: {:?}", source),
            }
        };

        let write_dest = |regs: &mut gpr::Regs, dest: &Operand, reg: u64, nat: bool| {
            match dest {
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
                Operand::GPRegister(yaxpeax_ia64::GPRegister(index)) | Operand::Memory(yaxpeax_ia64::GPRegister(index)) => {
                    eprintln!("r{} <= {:016x} {}", index, reg, if nat { "(NaT)" } else { "" });
                    regs.write_gpr(*index as usize, reg, nat).unwrap();
                },
                Operand::PredicateRegister(yaxpeax_ia64::PredicateRegister(index)) => {
                    assert!(!nat);
                    eprintln!("p{} <= {}", index, reg == 1);
                    regs.write_pr(*index as usize, reg == 1);
                }
                _ => todo!("dest: {:?}", dest),
            }
        };

        match instruction.opcode() {
            Opcode::Addl => {
                if !pred { return Action::Continue; }
                let operands = instruction.operands();
                let (source1, nat1) = read_source(&self.regs, &operands[1]);
                let (source2, nat2) = read_source(&self.regs, &operands[2]);
                write_dest(&mut self.regs, &operands[0], source1 + source2, nat1 || nat2);
                Action::Continue
            },
            Opcode::Br_cond => {
                if !pred { return Action::Continue; }
                let ip = match instruction.operands()[0] {
                    Operand::ImmI64(imm) => ((self.regs.read_ip() as i64) + imm) as u64,
                    Operand::BranchRegister(yaxpeax_ia64::BranchRegister(br)) => self.regs.read_br(br as usize),
                    _ => todo!("br_cond source: {:?}", instruction.operands()[0]),
                };
                self.regs.write_ip(ip);
                Action::BranchTaken
            },
            Opcode::Break_m => {
                if !pred { return Action::Continue; }
                panic!("Break Instruction");
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
            Opcode::Flushrs => {
                eprintln!("flushrs stubbed");
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
                    write_dest(&mut self.regs, &operands[1], source + offset, false);
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
                    write_dest(&mut self.regs, &operands[1], source + offset, false);
                }
                Action::Continue
            },
            Opcode::Mov | Opcode::Movl => {
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
            _ => todo!("{:?} {0}", instruction),
        }
    }

    pub fn step_bundle(&mut self) {
        let ip = self.regs.read_ip();
        let bytes = self.read16(ip);
        let decoder = yaxpeax_ia64::InstDecoder::default();
        let bundle = decoder.decode(bytes.iter().copied()).unwrap();
        println!("{:016x}: {}", ip, bundle);

        let mut branch_taken = false;
        for instruction in bundle.instructions() {
            match self.step_instruction(instruction) {
                Action::Continue => {},
                Action::BranchTaken => {
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

