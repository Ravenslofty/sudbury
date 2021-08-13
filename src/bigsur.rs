use std::convert::TryInto;

use yaxpeax_ia64::DecodeError;

use crate::action::Action;
use crate::merced::Merced;
use crate::mmio::Mmio;

pub struct BigSurState {
    rom: Box<[u8]>,
}

impl Mmio for BigSurState {
    fn read1(&self, address: u64) -> u8 {
        todo!()
    }

    fn read8(&self, address: u64) -> u64 {
        todo!()
    }

    fn read16(&self, address: u64) -> u128 {
        match address {
            // BIOS ROM.
            0xFFC0_0000 ..= 0xFFFF_FFFF => {
                let address = (address - 0xFFC0_0000) as usize;
                u128::from_le_bytes(self.rom[address..address + 16].try_into().unwrap())
            },
            _ => unimplemented!("read16 from {:016x}", address),
        }
    }
}

pub struct BigSur {
    state: BigSurState,
    cpu: Merced,
}

impl BigSur {
    pub fn new(rom: Box<[u8]>) -> Self {
        let state = BigSurState {
            rom
        };

        let mut bigsur = Self {
            state,
            cpu: Merced::new(),
        };

        bigsur.cpu.reset_exception();
        bigsur
    }

    pub fn run(&mut self) -> Result<(), DecodeError> {
        loop {
            let ip = self.cpu.ip();
            let trace = self.cpu.build_trace(ip, &mut self.state)?;

            for f in trace {
                if let Action::BranchTaken = f() {
                    break;
                }
            }
        }
    }
}
