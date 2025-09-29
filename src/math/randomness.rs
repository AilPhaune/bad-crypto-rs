pub trait CryptographicallySecureRandomIntegerGenerator {
    fn get_bytes(&mut self, out: &mut [u8]) -> Option<()>;
}

#[cfg(test)]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct TestRandomIntegerGenerator {
    state: u8,
}
#[cfg(test)]
impl Default for TestRandomIntegerGenerator {
    fn default() -> Self {
        let state = match std::time::SystemTime::now().duration_since(std::time::UNIX_EPOCH) {
            Ok(duration) => (duration.as_nanos() & 0xFF) as u8,
            Err(_) => 0,
        };
        Self { state }
    }
}

#[cfg(test)]
impl CryptographicallySecureRandomIntegerGenerator for TestRandomIntegerGenerator {
    fn get_bytes(&mut self, out: &mut [u8]) -> Option<()> {
        for byte in out.iter_mut() {
            *byte = self.state;
            self.state = self.state.wrapping_add(1);
        }
        Some(())
    }
}
