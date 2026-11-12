#!/usr/bin/env python3
"""Aspis translatability pass, patch 3 (on top of patches 0 to 2): r1_semantic::claims without raw pointers and
without a loop. Same order of effects: the record lookup, the fallible allocation, then the three decodes at value
offsets 0, 29, 58. The shape is the one of R1's rewritten `candidate_claims::claims` (the text R1's model
ClaimsUnrolledParentSource was emitted from): zero-filled vector, boxed slice, conversion to the boxed array, then the
three assignments. That Rust file is no longer on the host and is not in this worktree; the text here is reconstructed
from the emitted Lean (codex-cx-sound-int2-20261025/source-inputs/ClaimsUnrolledParentSource.lean: function at lines
5 to 17 of src/candidate_claims.rs, the two error closures at 8:17-8:38 and 12:17-12:38, order of calls as emitted).
It could not be compared with the original byte for byte. usage: TP_rewrite_p3.py <tree dir> <out dir>"""
import sys
from pathlib import Path
T, OUT = Path(sys.argv[1]), Path(sys.argv[2]); f = 'crates/aspis-r1-cost-probe/src/r1_semantic.rs'
t = (T / f).read_text()
old = '''    let record = prefix.validated_record(25)?;
    let mut out =
        aspis_core::r0::heap::uninit::<[[QM31; 29]; 3]>().map_err(|_| Error::Allocation)?;
    unsafe {
        for p in 0..3 {
            out.as_mut_ptr()
                .cast::<[QM31; 29]>()
                .add(p)
                .write(record.decode_k::<29>(p * 29)?);
        }
        Ok(out.assume_init())
    }
}
'''
new = '''    let record = prefix.validated_record(25)?;
    let out = aspis_core::r0::heap::filled(3, [QM31::ZERO; 29])
        .map_err(|_| Error::Allocation)?;
    let mut out: Box<[[QM31; 29]; 3]> = out
        .into_boxed_slice()
        .try_into()
        .map_err(|_| Error::Allocation)?;
    out[0] = record.decode_k::<29>(0)?;
    out[1] = record.decode_k::<29>(29)?;
    out[2] = record.decode_k::<29>(58)?;
    Ok(out)
}

#[cfg(test)]
mod claims_tests {
    use super::*;
    /// The pinned form of `claims` (raw-pointer initialisation in a loop), verbatim, as the oracle.
    fn claims_pinned(prefix: &Prefix<'_>) -> Result<Box<[[QM31; 29]; 3]>, Error> {
        let record = prefix.validated_record(25)?;
        let mut out =
            aspis_core::r0::heap::uninit::<[[QM31; 29]; 3]>().map_err(|_| Error::Allocation)?;
        unsafe {
            for p in 0..3 {
                out.as_mut_ptr()
                    .cast::<[QM31; 29]>()
                    .add(p)
                    .write(record.decode_k::<29>(p * 29)?);
            }
            Ok(out.assume_init())
        }
    }
    /// On the semantic prefix of each saved proof (expanded as the verifier expands it) the two forms agree.
    #[test]
    fn claims_equals_the_pinned_form_on_the_saved_proofs() {
        macro_rules! proof {
            ($name:literal) => {
                include_bytes!(concat!(env!("CARGO_MANIFEST_DIR"), "/../../docs/research/100bit-spend-path-20261013/evidence/format-adopt-20261019/fixtures/", $name, "/r1-s2-proof.bin")) as &[u8]
            };
        }
        let mut compared = 0;
        for (name, proof) in [("transfer-13", proof!("transfer-13")), ("transfer-255", proof!("transfer-255")), ("transfer-1023", proof!("transfer-1023")), ("withdrawal-13", proof!("withdrawal-13")), ("withdrawal-255", proof!("withdrawal-255")), ("withdrawal-1023", proof!("withdrawal-1023"))] {
            let mut semantic = alloc::vec![0u8; crate::compact::LOGICAL_SEMANTIC];
            crate::compact::expand_semantic(&proof[crate::compact::OFF_SEMANTIC..crate::compact::OFF_Y1], &mut semantic).unwrap();
            let prefix = match Prefix::parse(&semantic) { Ok(p) => p, Err(_) => panic!("{name}: prefix") };
            assert!(claims(&prefix).map(|b| *b) == claims_pinned(&prefix).map(|b| *b), "{name}");
            assert!(claims(&prefix).is_ok(), "{name}");
            compared += 1;
        }
        assert_eq!(compared, 6);
    }
}
'''
assert t.count(old) == 1
(OUT / f).parent.mkdir(parents=True, exist_ok=True); (OUT / f).write_text(t.replace(old, new)); print('wrote', f)
