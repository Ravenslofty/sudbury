pub trait Mmio {
    /// Read a byte.
    // TODO: read may fail.
    fn read1(&self, address: u64) -> u8;

    /// Read 8 bytes.
    // TODO: read may fail.
    fn read8(&self, address: u64) -> u64;

    /// Read 16 bytes.
    // TODO: read may fail.
    fn read16(&self, address: u64) -> u128;
}