pub struct Regs {
    /// General-purpose registers.
    /// r0 reads as zero, writes trap.
    gpr: [u64; 128],
    /// General-purpose register not-a-thing (NaT) bits.
    /// r0 is always-false since r0 the register is a constant.
    gpr_nat: [bool; 128],
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
    /// Processor status register.
    psr: u64,
    /// Control registers.
    cr: [u64; 128],
}

impl Regs {
    pub fn new() -> Self {
        let gpr = [0_u64; 128];
        let gpr_nat = [false; 128];
        let mut fpr = [0.0_f64; 128];
        let pr = [true; 64];
        let br = [0; 8];
        let ip = 0;
        let ar = [0; 128];
        let psr = 0;
        let cr = [0; 128];

        // f1 is a constant 1.0.
        fpr[1] = 1.0_f64;
        
        Self { gpr, gpr_nat, fpr, pr, br, ip, ar, psr, cr }
    }

    pub fn read_gpr(&self, index: usize) -> (u64, bool) {
        (self.gpr[index], self.gpr_nat[index])
    }

    pub fn write_gpr(&mut self, index: usize, reg: u64, nat: bool) -> Result<(), ()> {
        if index == 0 {
            return Err(());
        }
        self.gpr[index] = reg;
        self.gpr_nat[index] = nat;
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
        Err(())
    }

    pub fn write_ar(&mut self, index: usize, reg: u64) -> Result<(), ()> {
        Err(())
    }

    pub fn read_psr(&self) -> u64 {
        self.psr
    }

    pub fn read_cr(&self, index: usize) -> Result<u64, ()> {
        // ar18 = BSPSTORE
        Err(())
    }

    pub fn write_cr(&mut self, index: usize, reg: u64) -> Result<(), ()> {
        assert_eq!(index, 64);
        self.cr[index] = reg;
        Ok(())
    }
}