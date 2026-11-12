#!/usr/bin/env python3
"""Aspis translatability pass, patch 2 (on top of patches 0 and 1): the two R1 functions on the hot path that neither
tool pair translates and that have no settled text (soundness lead's ruling): canonical_scan and
QueryGeometry::for_range. One definition for both configurations.
usage: TP_rewrite_p2.py <tree dir> <out dir> [scan form]
scan form (default `unrolled2`, the form of the patch): several forms of canonical_scan were written to find one that
the tools translate AND that costs no more than the budget; each is the same checks in the same order. Compute against
the pinned nest on the recorded payments (bisect run b3): split, subslice, bool +4,133; unrolled, unrolled2,
subslice-unrolled -771; flag about +20,700.
  pinned            no change (the tools reject it: "Continue to outer loops are not supported yet")
  split             each loop in its own #[inline(always)] function, `?` inside single loops
  subslice          as split, the helpers receive the slot's own bytes
  unrolled          one helper per slot (one loop, then three straight-line checks); the four slots written out
                    (the tools reject the helper: "Unexpected return", a loop with `?` followed by more `?`)
  unrolled2         as unrolled, the 26-limb loop in a helper of its own, so that every function is either one loop
                    followed by `Ok(())` or straight-line code
  subslice-unrolled as unrolled, the helper receives the slot's own bytes
  bool              as split, the two inner helpers return bool
  flag              the nest kept, a flag in place of the early return (no `?` in a loop; a rejected proof costs the
                    full scan). Measured at about 20,700 compute units more than the pinned form: not usable.
  a form name followed by `+never` gives the per-opening helper #[inline(never)]."""
import re, sys
from pathlib import Path
T, OUT = Path(sys.argv[1]), Path(sys.argv[2]); C = 'crates/aspis-r1-cost-probe/src/'
MODE = sys.argv[3] if len(sys.argv) > 3 else 'unrolled2'
NEVER = MODE.endswith('+never'); FORM = MODE[:-6] if NEVER else MODE
def sub(t, old, new):
    assert t.count(old) == 1, ('count', old[:90], t.count(old)); return t.replace(old, new)
out = {}
f = C + 'candidate.rs'; t = (T / f).read_text()
NEST = """    for i in 0..22 {
        let q = opening(proof, i);
        for s in 0..4 {
            for l in 0..26 {
                M31::from_le_bytes(q[s * 120 + l * 4..s * 120 + l * 4 + 4].try_into().unwrap()).ok_or(Error::Parse)?;
            }
            K::from_le_bytes(&q[s * 120 + 104..s * 120 + 120]).ok_or(Error::Parse)?;
            for l in 0..2 {
                K::from_le_bytes(&q[480 + s * 32 + l * 16..480 + s * 32 + l * 16 + 16]).ok_or(Error::Parse)?;
            }
        }
        echeck(&q[672..800], false)?;
    }
    Ok(())
}
"""
AFTER = "/// Aspis new gate (replaces the pinned `canonical_scan`"
MAIN = """    for i in 0..22 {
        scan_opening(opening(proof, i))?;
    }
    Ok(())
}
"""
ATTR = '#[cfg(not(feature = "future-word-scan"))]\n#[inline(always)]\n'
OPEN = '#[cfg(not(feature = "future-word-scan"))]\n' + ('#[inline(never)]\n' if NEVER else '#[inline(always)]\n')
FORMS = {
 'split': '/// The 26 base-field limbs of slot `s` of one opening.\n' + ATTR + """fn scan_slot_base(q: &[u8], s: usize) -> Result<(), Error> {
    for l in 0..26 {
        M31::from_le_bytes(q[s * 120 + l * 4..s * 120 + l * 4 + 4].try_into().unwrap()).ok_or(Error::Parse)?;
    }
    Ok(())
}
/// The two C2 values of slot `s` of one opening.
""" + ATTR + """fn scan_slot_extension(q: &[u8], s: usize) -> Result<(), Error> {
    for l in 0..2 {
        K::from_le_bytes(&q[480 + s * 32 + l * 16..480 + s * 32 + l * 16 + 16]).ok_or(Error::Parse)?;
    }
    Ok(())
}
/// One opening: per slot the base limbs, the C1 tail value and the two C2 values, then the folded values.
""" + OPEN + """fn scan_opening(q: &[u8]) -> Result<(), Error> {
    for s in 0..4 {
        scan_slot_base(q, s)?;
        K::from_le_bytes(&q[s * 120 + 104..s * 120 + 120]).ok_or(Error::Parse)?;
        scan_slot_extension(q, s)?;
    }
    echeck(&q[672..800], false)
}
""",
 'subslice': '/// The 26 base-field limbs of one slot (`slot` is its first 104 bytes).\n' + ATTR + """fn scan_slot_base(slot: &[u8]) -> Result<(), Error> {
    for l in 0..26 {
        M31::from_le_bytes(slot[l * 4..l * 4 + 4].try_into().unwrap()).ok_or(Error::Parse)?;
    }
    Ok(())
}
/// The two C2 values of one slot (`pair` is their 32 bytes).
""" + ATTR + """fn scan_slot_extension(pair: &[u8]) -> Result<(), Error> {
    for l in 0..2 {
        K::from_le_bytes(&pair[l * 16..l * 16 + 16]).ok_or(Error::Parse)?;
    }
    Ok(())
}
/// One opening: per slot the base limbs, the C1 tail value and the two C2 values, then the folded values.
""" + OPEN + """fn scan_opening(q: &[u8]) -> Result<(), Error> {
    for s in 0..4 {
        scan_slot_base(&q[s * 120..s * 120 + 104])?;
        K::from_le_bytes(&q[s * 120 + 104..s * 120 + 120]).ok_or(Error::Parse)?;
        scan_slot_extension(&q[480 + s * 32..480 + s * 32 + 32])?;
    }
    echeck(&q[672..800], false)
}
""",
 'unrolled': '/// Slot `s` of one opening: the 26 base-field limbs, the C1 tail value, the two C2 values.\n' + ATTR + """fn scan_slot(q: &[u8], s: usize) -> Result<(), Error> {
    for l in 0..26 {
        M31::from_le_bytes(q[s * 120 + l * 4..s * 120 + l * 4 + 4].try_into().unwrap()).ok_or(Error::Parse)?;
    }
    K::from_le_bytes(&q[s * 120 + 104..s * 120 + 120]).ok_or(Error::Parse)?;
    K::from_le_bytes(&q[480 + s * 32..480 + s * 32 + 16]).ok_or(Error::Parse)?;
    K::from_le_bytes(&q[480 + s * 32 + 16..480 + s * 32 + 32]).ok_or(Error::Parse)?;
    Ok(())
}
/// One opening: its four slots in order, then the folded values.
""" + OPEN + """fn scan_opening(q: &[u8]) -> Result<(), Error> {
    scan_slot(q, 0)?;
    scan_slot(q, 1)?;
    scan_slot(q, 2)?;
    scan_slot(q, 3)?;
    echeck(&q[672..800], false)
}
""",
 'unrolled2': '/// The 26 base-field limbs of slot `s` of one opening.\n' + ATTR + """fn scan_slot_base(q: &[u8], s: usize) -> Result<(), Error> {
    for l in 0..26 {
        M31::from_le_bytes(q[s * 120 + l * 4..s * 120 + l * 4 + 4].try_into().unwrap()).ok_or(Error::Parse)?;
    }
    Ok(())
}
/// Slot `s` of one opening: the 26 base-field limbs, the C1 tail value, the two C2 values.
""" + ATTR + """fn scan_slot(q: &[u8], s: usize) -> Result<(), Error> {
    scan_slot_base(q, s)?;
    K::from_le_bytes(&q[s * 120 + 104..s * 120 + 120]).ok_or(Error::Parse)?;
    K::from_le_bytes(&q[480 + s * 32..480 + s * 32 + 16]).ok_or(Error::Parse)?;
    K::from_le_bytes(&q[480 + s * 32 + 16..480 + s * 32 + 32]).ok_or(Error::Parse)?;
    Ok(())
}
/// One opening: its four slots in order, then the folded values.
""" + OPEN + """fn scan_opening(q: &[u8]) -> Result<(), Error> {
    scan_slot(q, 0)?;
    scan_slot(q, 1)?;
    scan_slot(q, 2)?;
    scan_slot(q, 3)?;
    echeck(&q[672..800], false)
}
""",
 'subslice-unrolled': '/// One slot: the 26 base-field limbs and the C1 tail value (`slot`, 120 bytes), the two C2 values (`pair`, 32 bytes).\n' + ATTR + """fn scan_slot(slot: &[u8], pair: &[u8]) -> Result<(), Error> {
    for l in 0..26 {
        M31::from_le_bytes(slot[l * 4..l * 4 + 4].try_into().unwrap()).ok_or(Error::Parse)?;
    }
    K::from_le_bytes(&slot[104..120]).ok_or(Error::Parse)?;
    K::from_le_bytes(&pair[..16]).ok_or(Error::Parse)?;
    K::from_le_bytes(&pair[16..32]).ok_or(Error::Parse)?;
    Ok(())
}
/// One opening: its four slots in order, then the folded values.
""" + OPEN + """fn scan_opening(q: &[u8]) -> Result<(), Error> {
    scan_slot(&q[0..120], &q[480..512])?;
    scan_slot(&q[120..240], &q[512..544])?;
    scan_slot(&q[240..360], &q[544..576])?;
    scan_slot(&q[360..480], &q[576..608])?;
    echeck(&q[672..800], false)
}
""",
 'bool': '/// The 26 base-field limbs of slot `s` of one opening are canonical.\n' + ATTR + """fn scan_slot_base(q: &[u8], s: usize) -> bool {
    for l in 0..26 {
        if M31::from_le_bytes(q[s * 120 + l * 4..s * 120 + l * 4 + 4].try_into().unwrap()).is_none() {
            return false;
        }
    }
    true
}
/// The two C2 values of slot `s` of one opening are canonical.
""" + ATTR + """fn scan_slot_extension(q: &[u8], s: usize) -> bool {
    for l in 0..2 {
        if K::from_le_bytes(&q[480 + s * 32 + l * 16..480 + s * 32 + l * 16 + 16]).is_none() {
            return false;
        }
    }
    true
}
/// One opening: per slot the base limbs, the C1 tail value and the two C2 values, then the folded values.
""" + OPEN + """fn scan_opening(q: &[u8]) -> Result<(), Error> {
    for s in 0..4 {
        if !scan_slot_base(q, s) {
            return Err(Error::Parse);
        }
        K::from_le_bytes(&q[s * 120 + 104..s * 120 + 120]).ok_or(Error::Parse)?;
        if !scan_slot_extension(q, s) {
            return Err(Error::Parse);
        }
    }
    echeck(&q[672..800], false)
}
""",
}
FLAG = """    let mut canonical = true;
    for i in 0..22 {
        let q = opening(proof, i);
        for s in 0..4 {
            for l in 0..26 {
                canonical &= M31::from_le_bytes(q[s * 120 + l * 4..s * 120 + l * 4 + 4].try_into().unwrap()).is_some();
            }
            canonical &= K::from_le_bytes(&q[s * 120 + 104..s * 120 + 120]).is_some();
            for l in 0..2 {
                canonical &= K::from_le_bytes(&q[480 + s * 32 + l * 16..480 + s * 32 + l * 16 + 16]).is_some();
            }
        }
        canonical &= echeck(&q[672..800], false).is_ok();
    }
    if canonical {
        Ok(())
    } else {
        Err(Error::Parse)
    }
}
"""
if FORM == 'flag':
    t = sub(t, NEST + AFTER, FLAG + AFTER)
elif FORM != 'pinned':
    t = sub(t, NEST + AFTER, MAIN + FORMS[FORM] + AFTER)
out[f] = t
f = C + 'verifier.rs'; t = (T / f).read_text()
# for_range: the backward pass in a function of its own, beside `batch_prefix_products` (which the pinned text already
# has for the forward pass), as a counting loop instead of a reversed range iterator. Inside `for_range` the tools
# reject the loop in either form ("Could not match the contexts").
t = sub(t, """        let mut suffix_inverse=product.inv();
        let mut flat_inverse=Vec::with_capacity(flat.len());
        flat_inverse.resize(flat.len(),M31::ZERO);
        for i in (0..flat.len()).rev() {
            flat_inverse[i]=suffix_inverse.mul(prefixes[i]);
            suffix_inverse=suffix_inverse.mul(flat[i]);
        }
""", """        let flat_inverse=batch_suffix_inverses(&flat,&prefixes,product);
""")
t = sub(t, """impl QueryGeometry {
    fn for_range(""", """/// The backward pass of the batch inversion: entry `i` is the inverse of `flat[i]`, from the inverse of the product
/// of all entries and the prefix products.
#[inline(always)]
fn batch_suffix_inverses(flat:&[M31],prefixes:&[M31],product:M31)->Vec<M31> {
    let mut suffix_inverse=product.inv();
    let mut flat_inverse=Vec::with_capacity(flat.len());
    flat_inverse.resize(flat.len(),M31::ZERO);
    let mut i=flat.len();
    while i>0 {
        i-=1;
        flat_inverse[i]=suffix_inverse.mul(prefixes[i]);
        suffix_inverse=suffix_inverse.mul(flat[i]);
    }
    flat_inverse
}

/// The five inverses of each query, in query order, taken from the flat vector.
#[inline(always)]
fn group_inverses(flat_inverse:&[M31],count:usize)->Vec<[M31;5]> {
    let mut inverses=Vec::with_capacity(count);
    let mut i=0;
    while i<count {
        inverses.push([flat_inverse[5*i],flat_inverse[5*i+1],flat_inverse[5*i+2],flat_inverse[5*i+3],flat_inverse[5*i+4]]);
        i+=1;
    }
    inverses
}

impl QueryGeometry {
    fn for_range(""")
# the last step of for_range: a counting loop in a helper in place of `map` over a range with `from_fn` and `collect`
# (two closures and two iterator adapters, for which the R1 library has no model)
# the zero test of the five values: the same five comparisons in the same order, without the iterator and its closure
t = sub(t, """            if values.iter().any(|x|*x==M31::ZERO){return Err(Error::Query);}
""", """            if circle_x==M31::ZERO||circle_y==M31::ZERO||line_x==M31::ZERO||line_y==M31::ZERO||line_z==M31::ZERO {return Err(Error::Query);}
""")
t = sub(t, """        let inverses=(0..line_z_values.len()).map(|i|core::array::from_fn(|j|flat_inverse[5*i+j])).collect();
""", """        let inverses=group_inverses(&flat_inverse,line_z_values.len());
""")
out[f] = t
# differential oracles (tests only): the pinned forms, verbatim
f = C + 'candidate.rs'; t = out[f]
if FORM != 'pinned':
    t = sub(t, "// FUTURE-VERSION EXPERIMENT (branch `future-version`): single-invocation\n", """#[cfg(all(test, not(feature = "future-word-scan")))]
mod canonical_scan_tests {
    use super::*;
    /// The reshaped scan against the pinned nested-loop form (`canonical_scan_pinned`): on an all-zero buffer,
    /// and with every 32-bit limb position from the first scanned byte to the end of the openings set to P.
    #[test]
    fn reshaped_scan_equals_the_pinned_scan() {
        let mut proof = alloc::vec![0u8; compact::PROOF_BYTES];
        assert_eq!(canonical_scan(&proof), Ok(()));
        assert_eq!(canonical_scan(&proof), canonical_scan_pinned(&proof));
        let p = 0x7fff_ffffu32.to_le_bytes();
        let mut at = compact::OFF_Y1;
        while at + 4 <= compact::OFF_NODES {
            let saved: [u8; 4] = proof[at..at + 4].try_into().unwrap();
            proof[at..at + 4].copy_from_slice(&p);
            assert_eq!(canonical_scan(&proof), canonical_scan_pinned(&proof), "limb at {at}");
            proof[at..at + 4].copy_from_slice(&saved);
            at += 4;
        }
    }
}

// FUTURE-VERSION EXPERIMENT (branch `future-version`): single-invocation
""")
out[f] = t
f = C + 'verifier.rs'; t = out[f]
t = sub(t, "#[inline(always)]\nfn circle_fold_with_inverses(", """#[cfg(test)]
mod for_range_tests {
    use super::*;
    /// The pinned backward pass of `for_range` (reversed range iterator), verbatim, as the oracle.
    fn backward_pinned(flat:&[M31],prefixes:&[M31],product:M31)->Vec<M31> {
        let mut suffix_inverse=product.inv();
        let mut flat_inverse=Vec::with_capacity(flat.len());
        flat_inverse.resize(flat.len(),M31::ZERO);
        for i in (0..flat.len()).rev() {
            flat_inverse[i]=suffix_inverse.mul(prefixes[i]);
            suffix_inverse=suffix_inverse.mul(flat[i]);
        }
        flat_inverse
    }
    #[test]
    fn for_range_inverses_equal_the_pinned_backward_pass() {
        let mut state=0x9e37_79b9_7f4a_7c15u64;
        for case in 0..200 {
            let mut queries=[0u32;22];
            for q in queries.iter_mut() {state^=state<<13;state^=state>>7;state^=state<<17;*q=(state%(1<<18)) as u32;}
            for (start,end) in [(0usize,22usize),(0,10),(10,22),(5,5)] {
                let g=match QueryGeometry::for_range(&queries,start,end) {Ok(g)=>g,Err(_)=>continue};
                let mut flat=Vec::new();
                for &query in &queries[start..end] {
                    let u=query as usize;
                    let domain::Point{x,y}=crate::fast_domain::fibre_point(domain::FibreIndex::new(u).unwrap());
                    let lx=crate::fast_domain::line_node(domain::FibreIndex::new(u/4*4).unwrap());
                    let ly=crate::fast_domain::line_node(domain::FibreIndex::new(u/4*4+3).unwrap());
                    flat.extend_from_slice(&[x,y,lx,ly,lx.mul(lx).double().sub(M31::ONE)]);
                }
                if flat.is_empty() {assert!(g.inverses.is_empty());continue;}
                let (prefixes,product)=batch_prefix_products(&flat);
                let expect=backward_pinned(&flat,&prefixes,product);
                assert_eq!(g.inverses.len(),end-start);
                for i in 0..g.inverses.len() {for j in 0..5 {assert_eq!(g.inverses[i][j],expect[5*i+j],"case {case}");}}
            }
        }
    }
}
#[inline(always)]
fn circle_fold_with_inverses(""")
out[f] = t
for p, text in out.items():
    q = OUT / p; q.parent.mkdir(parents=True, exist_ok=True); q.write_text(text); print('wrote', p)
