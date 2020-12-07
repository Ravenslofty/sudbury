use std::{fs::File, io::Read};

use sudbury::Cpu;

fn main() {
    let mut rom_file = File::open("/home/lofty/ia64sim/itanium-bios.bin").unwrap();
    let mut rom = Vec::new();
    rom_file.read_to_end(&mut rom).unwrap();
    let mut cpu = Cpu::new(rom);

    loop {
        cpu.step_bundle();
    }
}