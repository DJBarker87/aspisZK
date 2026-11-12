#!/usr/bin/env python3
"""X1 stage 2, item F: compact::expand_values with an index loop in place of chunks_exact(16).zip(chunks_exact_mut(32)).
Same length check and error; the same bytes written in the same order (value k: 16 copied bytes, then 16 zero bytes).
A differential test keeps the old body under cfg(test)."""
import sys
from pathlib import Path
T = Path(sys.argv[1]); assert 'src-frz-a' not in str(T)
p = T / 'crates/aspis-r1-cost-probe/src/compact.rs'; t = p.read_text()
old = '''    for (c, o) in compact.chunks_exact(16).zip(out.chunks_exact_mut(32)) {
        o[..16].copy_from_slice(c);
        o[16..].fill(0);
    }
    Ok(())
}
'''
new = '''    // Index form of `for (c, o) in compact.chunks_exact(16).zip(out.chunks_exact_mut(32))` (the translator's library
    // has no model of the zipped chunk iterators): value k is compact[16k..16k+16] -> out[32k..32k+16], then zeros.
    let values = compact.len() / 16;
    let mut k = 0;
    while k < values {
        out[32 * k..32 * k + 16].copy_from_slice(&compact[16 * k..16 * k + 16]);
        out[32 * k + 16..32 * k + 32].fill(0);
        k += 1;
    }
    Ok(())
}

/// X1 rewrite of `expand_values`: differential check against the frozen body (3d700effcab compact.rs 127-136).
#[cfg(test)]
mod x1_expand_values_rewrite {
    extern crate std;
    use super::*;

    fn old_expand_values(compact: &[u8], out: &mut [u8]) -> Result<(), CodecError> {
        if compact.len() % 16 != 0 || out.len() != 2 * compact.len() {
            return Err(CodecError::Length);
        }
        for (c, o) in compact.chunks_exact(16).zip(out.chunks_exact_mut(32)) {
            o[..16].copy_from_slice(c);
            o[16..].fill(0);
        }
        Ok(())
    }

    #[test]
    fn same_output_and_error() {
        let mut state = 0x9e37_79b9_7f4a_7c15u64;
        for n in [0usize, 1, 15, 16, 17, 31, 32, 48, 160, 1600, 16 * 300] {
            for extra in [0usize, 1, 16, 32] {
                for fill in [0u8, 0xa5, 0xff] {
                    let compact: std::vec::Vec<u8> = (0..n).map(|_| { state = state.wrapping_mul(6364136223846793005).wrapping_add(1); (state >> 56) as u8 }).collect();
                    for out_len in [2 * n, 2 * n + extra, (2 * n).saturating_sub(extra)] {
                        let mut a = std::vec![fill; out_len];
                        let mut b = a.clone();
                        assert_eq!(expand_values(&compact, &mut a), old_expand_values(&compact, &mut b), "{n} {out_len}");
                        assert_eq!(a, b, "{n} {out_len}");
                    }
                }
            }
        }
    }
}
'''
assert t.count(old) == 1; t = t.replace(old, new); p.write_text(t); print('ok')
