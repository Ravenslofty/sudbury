pub struct I460GX {
    undocumented_sac_feb00cb0: u32,
    bsp_select: u32,
}

impl I460GX {
    pub fn new() -> Self {
        Self {
            undocumented_sac_feb00cb0: 0,
            bsp_select: 1 << 7,
        }
    }

    pub fn read_sac_feb00cb0(&self) -> u32 {
        self.undocumented_sac_feb00cb0
    }

    pub fn write_sac_feb00cb0(&mut self, reg: u32) {
        self.undocumented_sac_feb00cb0 = reg;
    }

    pub fn read_bsp_select(&self) -> u32 {
        self.bsp_select
    }

    pub fn write_bsp_select(&mut self, reg: u32) {
        self.bsp_select = reg;
    }
}