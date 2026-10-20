// Generated exact method/struct cuts; see source-binding.json.
#[derive(Clone, Copy)]
pub struct M31(pub u32);
#[derive(Clone, Copy)]
pub struct CM31 { pub a: M31, pub b: M31 }
#[derive(Clone, Copy)]
pub struct QM31 { pub c0: CM31, pub c1: CM31 }
#[derive(Clone, Copy)]
pub struct WideExact {
    c0: QM31,
    c1: QM31,
}
impl WideExact {
    pub const LIMB_COUNT: usize = 8;
    pub const BYTE_LEN: usize = 32;
    pub const fn to_limbs(self) -> [u32; Self::LIMB_COUNT] {
        [
            self.c0.c0.a.0,
            self.c0.c0.b.0,
            self.c0.c1.a.0,
            self.c0.c1.b.0,
            self.c1.c0.a.0,
            self.c1.c0.b.0,
            self.c1.c1.a.0,
            self.c1.c1.b.0,
        ]
    }
    pub fn to_le_bytes(self) -> [u8; Self::BYTE_LEN] {
        let mut bytes = [0; Self::BYTE_LEN];
        for (chunk, limb) in bytes.chunks_exact_mut(4).zip(self.to_limbs()) {
            chunk.copy_from_slice(&limb.to_le_bytes());
        }
        bytes
    }
}

// Harness-only constructor; no canonicality assumption, all 256 input bits.
fn raw_wide(x: [u32; 8]) -> WideExact {
    WideExact {
      c0: QM31 { c0: CM31 { a:M31(x[0]),b:M31(x[1]) },
                  c1: CM31 { a:M31(x[2]),b:M31(x[3]) } },
      c1: QM31 { c0: CM31 { a:M31(x[4]),b:M31(x[5]) },
                  c1: CM31 { a:M31(x[6]),b:M31(x[7]) } },
    }
}

/// First-order executable projection of the P6 eight captured-start writes.
/// Forward traversal captures each chunk start and four-byte replacement;
/// unwind applies them from last to first, as the extracted back continuation.
fn captured_writeback(limbs: [u32;8], initial: [u8;32]) -> [u8;32] {
    let mut starts = [0usize;8];
    let mut chunks = [[0u8;4];8];
    let mut cursor = 0usize;
    let mut i = 0usize;
    while i < 8 {
        assert!(cursor + 4 <= 32);
        starts[i] = cursor;
        chunks[i] = limbs[i].to_le_bytes();
        cursor += 4;
        i += 1;
    }
    let mut source = initial;
    while i > 0 {
        i -= 1;
        let start = starts[i];
        let mut b = 0;
        while b < 4 {
            source[start + b] = chunks[i][b];
            b += 1;
        }
    }
    source
}

#[cfg(kani)]
#[kani::proof]
#[kani::unwind(34)]
fn original_serializer_matches_captured_writeback() {
    let limbs: [u32;8] = kani::any();
    let initial: [u8;32] = kani::any();
    assert_eq!(raw_wide(limbs).to_le_bytes(), captured_writeback(limbs, initial));
}

#[cfg(test)]
mod tests {
 use super::*;
 #[test]
 fn captured_starts_and_terminal_writeback_controls() {
    for limbs in [[0;8], [u32::MAX;8], [1,2,3,4,5,6,7,8],
        [0,1,u32::MAX,2147483646,2147483647,2147483648,0x80000000,0x01020304]] {
        let actual=raw_wide(limbs).to_le_bytes();
        assert_eq!(actual,captured_writeback(limbs,[0xa5;32]));
    }
    let limbs=[1,2,3,4,5,6,7,8];
    let actual=raw_wide(limbs).to_le_bytes();
    // Rejected historical bug 1: all callbacks read the final lastStart.
    let mut wrong_start=[0u8;32];
    for i in (0..8).rev() { wrong_start[28..32].copy_from_slice(&limbs[i].to_le_bytes()); }
    assert_ne!(actual,wrong_start);
    // Rejected historical bug 2: terminal hasLast=false suppresses writeback.
    assert_ne!(actual,[0u8;32]);
 }
}
