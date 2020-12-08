pub struct I460GX {
    undocumented_sac_feb00cb0: u32,
}

impl I460GX {
    pub fn new() -> Self {
        Self {
            undocumented_sac_feb00cb0: 0,
        }
    }

    pub fn read_sac_feb00cb0(&self) -> u32 {
        self.undocumented_sac_feb00cb0
    }

    pub fn write_sac_feb00cb0(&mut self, reg: u32) {
        self.undocumented_sac_feb00cb0 = reg;
    }
}