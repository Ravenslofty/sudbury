pub const AR_PFS: usize = 64;
pub const AR_LC: usize = 65;
pub const AR_EC: usize = 66;

pub const AR_PFS_PFM: u64 = 0x3FFFFFFFFF;
pub const AR_PFS_PEC: u64 = 0x3F << 52;
pub const AR_PFS_PPL: u64 = 0x3 << 62;

pub const CFM_SOF: u64 = 0x7F;
pub const CFM_SOL: u64 = 0x7F << 7;
pub const CFM_SOR: u64 = 0xF << 14;
pub const CFM_RRB: u64 = 0xFFFFF << 18;
pub const CFM_RRB_GR: u64 = 0x7F << 18;
pub const CFM_RRB_FR: u64 = 0x7F << 25;
pub const CFM_RRB_PR: u64 = 0x3F << 32;

pub const PSR_CPL: u64 = 3 << 32;
pub const PSR_BN: u64 = 1 << 44;

pub const CR_IPSR: usize = 16;
pub const CR_IIP: usize = 19;

pub struct Regs {
    /// General-purpose registers.
    /// r0 reads as zero, writes trap.
    gpr: [u64; 128],
    /// General-purpose register not-a-thing (NaT) bits.
    /// r0 is always-false since r0 the register is a constant.
    gpr_nat: [bool; 128],
    /// Banked general-purpose registers 16-31.
    gpr_bank: [u64; 16], 
    /// Banked general-purpose registers 16-31 not-a-thing (NaT) bits.
    gpr_bank_nat: [bool; 16],
    /// Floating-point registers.
    /// f0 reads as 0.0, writes trap.
    /// f1 reads as 1.0, writes trap.
    fpr: [f64; 128],
    /// Predicate registers.
    /// p0 reads as true, writes ignored.
    pr: [bool; 64],
    /// Branch registers.
    br: [u64; 8],
    /// Instruction pointer.
    ip: u64,
    /// Application registers.
    ar: [u64; 128],
    /// Current frame marker.
    cfm: u64,
    /// Processor status register.
    psr: u64,
    /// Control registers.
    cr: [u64; 128],
    /// CPU identification registers.
    cpuid: [u64; 5],
    /// Machine-specific registers. Yep.
    msr: [u64; 4096],
}

impl Regs {
    pub fn new() -> Self {
        let gpr = [0_u64; 128];
        let gpr_nat = [false; 128];
        let gpr_bank = [0_u64; 16];
        let gpr_bank_nat = [false; 16];
        let mut fpr = [0.0_f64; 128];
        let pr = [true; 64];
        let br = [0; 8];
        let ip = 0;
        let ar = [0; 128];
        let cfm = 0;
        let psr = 0;
        let cr = [0; 128];
        let mut cpuid = [0; 5];
        let msr = [0; 4096];

        // f1 is a constant 1.0.
        fpr[1] = 1.0_f64;

        cpuid[0] = u64::from_le_bytes([b'S', b'u', b'd', b'b', b'u', b'r', b'y', 0]);
        cpuid[3] = 4;
        
        eprintln!("Gpr size: {}", std::mem::size_of::<Self>());

        Self { gpr, gpr_nat, gpr_bank, gpr_bank_nat, fpr, pr, br, ip, ar, cfm, psr, cr, cpuid, msr }
    }

    pub fn read_gpr(&self, index: usize) -> (u64, bool) {
        if self.psr & PSR_BN == 0 || index < 16 || index > 31 {
            (self.gpr[index], self.gpr_nat[index])
        } else {
            (self.gpr_bank[index-16], self.gpr_bank_nat[index-16])
        }
    }

    pub fn write_gpr(&mut self, index: usize, reg: u64, nat: bool) -> Result<(), ()> {
        if index == 0 {
            return Err(());
        }
        if self.psr & PSR_BN == 0 || index < 16 || index > 31 {
            self.gpr[index] = reg;
            self.gpr_nat[index] = nat;
        } else {
            self.gpr_bank[index-16] = reg;
            self.gpr_bank_nat[index-16] = nat;
        }
        Ok(())
    }

    pub fn read_fpr(&self, index: usize) -> f64 {
        self.fpr[index]
    }

    pub fn write_fpr(&mut self, index: usize, reg: f64) -> Result<(), ()> {
        if index <= 1 {
            return Err(());
        }
        self.fpr[index] = reg;
        Ok(())
    }

    pub fn read_pr(&self, index: usize) -> bool {
        self.pr[index]
    }

    pub fn read_all_pr(&self) -> u64 {
        let mut x = 0_u64;
        for pr in &self.pr {
            x = (x << 1) | (*pr as u64);
        }
        x
    }

    pub fn write_all_pr(&mut self, reg: u64) {
        for bit in 0_usize..=63 {
            self.pr[bit] = (reg & (1 << bit)) != 0;
        }
    }

    pub fn write_pr(&mut self, index: usize, reg: bool) {
        if index == 0 {
            return;
        }
        self.pr[index] = reg;
    }

    pub fn read_br(&self, index: usize) -> u64 {
        self.br[index]
    }

    pub fn write_br(&mut self, index: usize, reg: u64) {
        self.br[index] = reg;
    }

    pub fn read_ip(&self) -> u64 {
        self.ip
    }

    pub fn write_ip(&mut self, reg: u64) {
        assert!(reg & 0xF == 0);
        self.ip = reg;
    } 

    pub fn read_ar(&self, index: usize) -> Result<u64, ()> {
        // ar18 = BSPSTORE
        Ok(self.ar[index])
    }

    pub fn write_ar(&mut self, index: usize, reg: u64) -> Result<(), ()> {
        self.ar[index] = reg;
        Ok(())
    }

    pub fn read_cfm(&self) -> u64 {
        self.cfm
    }

    pub fn write_cfm(&mut self, reg: u64) { 
        self.cfm = reg;
    }

    pub fn read_psr(&self) -> u64 {
        self.psr
    }

    pub fn write_psr(&mut self, reg: u64) {
        self.psr = reg;
    }

    pub fn read_cr(&self, index: usize) -> Result<u64, ()> {
        Ok(self.cr[index])
    }

    pub fn write_cr(&mut self, index: usize, reg: u64) -> Result<(), ()> {
        // assert_eq!(index, 64);
        self.cr[index] = reg;
        Ok(())
    }

    pub fn read_cpuid(&self, index: usize) -> u64 {
        self.cpuid[index]
    }

    pub fn read_msr(&self, index: usize) -> u64 {
        match index {
            0x5dd | 0x600 | 0x602 | 0x60e | 0x615 => self.msr[index],
            // <the6p4c> msr 0x612, bit 6: "make machine work bit. set to 1 to make machine work"
            0x612 => self.msr[index] | (1 << 6),
            _ => unimplemented!("read from msr {:03x}", index),
        }
    }

    pub fn write_msr(&mut self, index: usize, reg: u64) {
        match index {
            0x020 | 0x042 | 0x0e3 | 0x181 | 0x1e8 | 0x1e9 | 0x450 | 0x4c4 | 0x5dd | 0x600 | 0x601 | 0x602 | 0x60d | 0x612 | 0x615 => self.msr[index] = reg,
            _ => unimplemented!("write to msr {:03x}", index),
        }
    }

    pub fn bank_switch(&mut self, bank: u8) {
        assert!(bank == 0 || bank == 1);
        self.psr &= !PSR_BN;
        self.psr |= (bank as u64) << 44;
    }
}