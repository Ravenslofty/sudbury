use std::{error::Error, fs::File, io::Read};

// CPUs.
mod merced;

// Systems.
mod bigsur;

// Utility traits.
mod action;
mod mmio;

fn main() -> Result<(), Box<dyn Error>> {
    let mut rom_file = File::open("itanium-bios.bin").unwrap();
    let mut rom = Vec::new();
    rom_file.read_to_end(&mut rom).unwrap();
    let rom = rom.into_boxed_slice();
    let mut bigsur = bigsur::BigSur::new(rom);
    bigsur.run()?;
    Ok(())
}