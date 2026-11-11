#!/usr/bin/env python3
"""Aspis extraction probe: build the REWRITTEN COPY of five source files that the probe used to test whether the
recommended reshaping translates. Reads the files of one commit from Git, applies exact-text replacements (each old text
must occur exactly once) and writes the results to an output directory. Nothing in the repository is changed.
usage: XP_rewrite.py <commit> <out dir>      (run from the repository)"""
import subprocess, sys
from pathlib import Path
REV, OUT = sys.argv[1], Path(sys.argv[2])
C = 'crates/aspis-r1-cost-probe/src/'
def src(p): return subprocess.check_output(['git', 'show', REV + ':' + p]).decode()
def cut(t, a, b):
    """the text from the unique occurrence of a up to (not including) the next occurrence of b"""
    assert t.count(a) == 1, ('start not unique', a[:60], t.count(a))
    i = t.index(a); j = t.index(b, i + len(a)); return t[i:j]
def sub(t, old, new):
    assert t.count(old) == 1, ('old text not unique', old[:70], t.count(old)); return t.replace(old, new)
out = {}

# ---------------------------------------------------------------- fused.rs
t = src(C + 'fused.rs')
# (a) relation_view: the fallible read comes before the struct literal
t = sub(t, """    Ok(View {
        variant: Variant::S2,
        semantic: &[],
        y1: &[],
        inactive: E::from_le_bytes(&proof[compact::OFF_INACTIVE..compact::OFF_ROUND0]).ok_or(Error::Parse)?,
        round0: &proof[compact::OFF_ROUND0..compact::OFF_FOLDED_ROOT],
        folded_root: None,
        round1: &proof[compact::OFF_ROUND1..compact::OFF_FINAL],
        final_message: &proof[compact::OFF_FINAL..compact::OFF_OPENINGS],
        query_bytes: &[],
    })
}

/// The three batched quantities of stage C.""", """    let inactive = E::from_le_bytes(&proof[compact::OFF_INACTIVE..compact::OFF_ROUND0]).ok_or(Error::Parse)?;
    Ok(View {
        variant: Variant::S2,
        semantic: &[],
        y1: &[],
        inactive,
        round0: &proof[compact::OFF_ROUND0..compact::OFF_FOLDED_ROOT],
        folded_root: None,
        round1: &proof[compact::OFF_ROUND1..compact::OFF_FINAL],
        final_message: &proof[compact::OFF_FINAL..compact::OFF_OPENINGS],
        query_bytes: &[],
    })
}

/// The three batched quantities of stage C.""")
# (b) extension_lane: the four fallible pushes move to a helper with one loop
t = sub(t, """        for k in 0..4 {
            dots[k].push(circle[i][k], signed[k]).map_err(|_| Error::Parse)?;
        }
    }
    let [d0, d1, d2, d3] = dots;
    Ok([d0.finish(), d1.finish(), d2.finish(), d3.finish()])
}
""", """        push_k4(&mut dots, &circle[i], &signed)?;
    }
    let [d0, d1, d2, d3] = dots;
    Ok([d0.finish(), d1.finish(), d2.finish(), d3.finish()])
}

#[inline(always)]
fn push_k4(dots: &mut [KbyKDot; 4], c: &[K; 4], signed: &[K; 4]) -> Result<(), Error> {
    for k in 0..4 {
        match dots[k].push(c[k], signed[k]) { Ok(()) => {}, Err(_) => return Err(Error::Parse) }
    }
    Ok(())
}
#[inline(always)]
fn push_e4(dots: &mut [EbyKDot; 4], power: E, h: &[K; 4]) -> Result<(), Error> {
    for k in 0..4 {
        match dots[k].push(power, h[k]) { Ok(()) => {}, Err(_) => return Err(Error::Parse) }
    }
    Ok(())
}
#[inline(always)]
fn push_e(dot: &mut EbyKDot, value: E, scalar: K) -> Result<(), Error> {
    match dot.push(value, scalar) { Ok(()) => Ok(()), Err(_) => Err(Error::Parse) }
}
#[inline(always)]
fn finish_e4(dots: [EbyKDot; 4]) -> [E; 4] {
    let [d0, d1, d2, d3] = dots;
    [d0.finish(), d1.finish(), d2.finish(), d3.finish()]
}
/// First fold, left side, base lanes: each lane contracted once with its gamma power.
#[inline(always)]
fn first_fold_base(first: &mut [EbyKDot; 4], g: &[E; 29], h: &[[K; 4]]) -> Result<(), Error> {
    for lane in 0..26 {
        push_e4(first, g[lane], &h[lane])?;
    }
    Ok(())
}
/// First fold, left side, the three QM31 lanes. Pinned gamma indices: C2 lanes 26 and 27, C1 tail lane 28.
#[inline(always)]
fn first_fold_extension(first: &mut [EbyKDot; 4], g: &[E; 29], extension: &[[K; 4]; 3]) -> Result<(), Error> {
    for which in 0..3 {
        let power = g[if which == 2 { 28 } else { 26 + which }];
        push_e4(first, power, &extension[which])?;
    }
    Ok(())
}
/// First fold, right side, and the second fold's four cubic coefficients (the per-query loop of `fold_sums`).
#[inline(always)]
fn second_fold(openings: &[u8], queries: &[u32; 22], c: &Coefficients, geometry: &QueryGeometry, second: &mut [EbyKDot; 4], right: &mut EbyKDot) -> Result<(), Error> {
    for i in 0..QUERIES {
        let q = &openings[i * OPENING..(i + 1) * OPENING];
        let v: [E; 4] = core::array::from_fn(|s| field(&q[672..800], s));
        let u = v[0].add(v[1]);
        let w = v[2].add(v[3]);
        let d1 = v[0].sub(v[1]);
        let d2 = v[3].sub(v[2]);
        let l = &c.line[i];
        #[cfg(feature = "future-fold-shared")]
        {
            let [_, _, lx, ly, _] = *geometry.for_query(i);
            let p1 = d1.mul_m31(lx);
            let p2 = d2.mul_m31(ly);
            push_e(&mut second[0], u.add(w), l[0])?;
            push_e(&mut second[1], p1.add(p2), l[0])?;
            push_e(&mut second[2], u.sub(w), l[3])?;
            push_e(&mut second[3], p1.sub(p2), l[3])?;
        }
        #[cfg(not(feature = "future-fold-shared"))]
        {
            let _ = geometry;
            push_e(&mut second[0], u.add(w), l[0])?;
            push_e(&mut second[1], d1, l[1])?;
            push_e(&mut second[1], d2, l[2])?;
            push_e(&mut second[2], u.sub(w), l[3])?;
            push_e(&mut second[3], d1, l[4])?;
            push_e(&mut second[3], d2, l[5])?;
        }
        push_e(right, v[queries[i] as usize % 4], c.rho[i])?;
    }
    Ok(())
}
""")
# (c) fold_sums: straight-line body over the helpers above; feature choices by #[cfg], not `if cfg!`
old = cut(t, "    let c = coefficients(rho, geometry)?;\n    mark(obs, Phase::QueryPart(0, 0));", "/// The pinned final-weight accumulation")
t = sub(t, old, """    let c = coefficients(rho, geometry)?;
    mark(obs, Phase::QueryPart(0, 0));
    let mut first = [EbyKDot::new(), EbyKDot::new(), EbyKDot::new(), EbyKDot::new()];
    #[cfg(feature = "future-tight-base")]
    {
        let h = base_lanes_tight(openings, &c.circle)?;
        first_fold_base(&mut first, g, &h)?;
    }
    #[cfg(not(feature = "future-tight-base"))]
    {
        let mut h = [[K::ZERO; 4]; 26];
        for lane in 0..26 {
            h[lane] = base_lane(openings, &c.circle, lane);
        }
        first_fold_base(&mut first, g, &h)?;
    }
    mark(obs, Phase::QueryPart(0, 1));
    #[cfg(feature = "future-tight-ext")]
    let extension = extension_lanes_tight(openings, &c.circle)?;
    #[cfg(not(feature = "future-tight-ext"))]
    let extension = [extension_lane(openings, &c.circle, 0)?, extension_lane(openings, &c.circle, 1)?, extension_lane(openings, &c.circle, 2)?];
    first_fold_extension(&mut first, g, &extension)?;
    let lhs1 = cubic(alpha[0], finish_e4(first));
    mark(obs, Phase::QueryPart(0, 2));
    let mut second = [EbyKDot::new(), EbyKDot::new(), EbyKDot::new(), EbyKDot::new()];
    let mut right = EbyKDot::new();
    second_fold(openings, queries, &c, geometry, &mut second, &mut right)?;
    let rhs2 = cubic(alpha[1], finish_e4(second));
    mark(obs, Phase::QueryPart(0, 3));
    Ok(FoldSums { lhs1, rhs1: right.finish(), rhs2 })
}

""")
# (d) base_lanes_tight: the per-query work and the periodic fold become loop-only helpers; the fallible loop stands alone
old = cut(t, "#[inline(never)]\nfn base_lanes_tight(openings: &[u8], circle: &[[K; 4]]) -> Result<Vec<[K; 4]>, Error> {", "/// E6: the three QM31 lanes")
t = sub(t, old, """#[inline(always)]
fn base_query(acc: &mut [u64; 416], q: &[u8; 480], c: &[K; 4]) {
    let mut l = [0u64; 16];
    for k in 0..4 {
        l[4 * k] = u64::from(c[k].c0.a.0);
        l[4 * k + 1] = u64::from(c[k].c0.b.0);
        l[4 * k + 2] = u64::from(c[k].c1.a.0);
        l[4 * k + 3] = u64::from(c[k].c1.b.0);
    }
    for lane in 0..26 {
        let at = 4 * lane;
        let read = |o: usize| u64::from(u32::from_le_bytes([q[o], q[o + 1], q[o + 2], q[o + 3]]));
        let (v0, v1, v2, v3) = (read(at), read(120 + at), read(240 + at), read(360 + at));
        let u = v0 + v1;
        let w = v2 + v3;
        let x = v0 + P64 - v1;
        let y = v3 + P64 - v2;
        let fold = |z: u64| (z & P64) + (z >> 31);
        let signed = [fold(u + w), fold(x + y), fold(u + 2 * P64 - w), fold(x + 2 * P64 - y)];
        let base = 16 * lane;
        for k in 0..4 {
            for j in 0..4 {
                acc[base + 4 * k + j] += l[4 * k + j] * signed[k];
            }
        }
    }
}
#[inline(always)]
fn base_fold(acc: &mut [u64; 416]) {
    let mut t = 0;
    while t < 416 {
        acc[t] = (acc[t] & P64) + (acc[t] >> 31);
        t += 1;
    }
}
#[inline(always)]
fn base_accumulate(acc: &mut [u64; 416], openings: &[u8], circle: &[[K; 4]]) -> Result<(), Error> {
    for i in 0..QUERIES {
        let q: &[u8; 480] = openings[i * OPENING..i * OPENING + 480].try_into().map_err(|_| Error::Parse)?;
        base_query(acc, q, &circle[i]);
        if i % 3 == 2 {
            base_fold(acc);
        }
    }
    Ok(())
}
#[inline(never)]
fn base_lanes_tight(openings: &[u8], circle: &[[K; 4]]) -> Result<Vec<[K; 4]>, Error> {
    let mut acc = aspis_core::r0::heap::filled(26 * 16, 0u64).map_err(|_| Error::Allocation)?;
    {
        let acc: &mut [u64; 416] = (&mut acc[..]).try_into().map_err(|_| Error::Allocation)?;
        base_accumulate(acc, openings, circle)?;
    }
    let mut out = aspis_core::r0::heap::filled(26, [K::ZERO; 4]).map_err(|_| Error::Allocation)?;
    for lane in 0..26 {
        for k in 0..4 {
            let at = 16 * lane + 4 * k;
            out[lane][k] = k_of([acc[at], acc[at + 1], acc[at + 2], acc[at + 3]]);
        }
    }
    Ok(out)
}

""")
# (e) summed_final_checks: each fallible loop in its own function; the body is straight-line
old = cut(t, "    let mut t = Transcript::resume(hash, p.state);\n    let lambda = t.scalar_k(ROW_CLAIMS, &claims_bytes(claim, rhs2));\n    let mut current = claim.add(rhs2.mul_qm31(lambda));", "fn claims_bytes(claim: E, rhs2: E) -> [u8; 64] {")
t = sub(t, old, """    let mut t = Transcript::resume(hash, p.state);
    let lambda = t.scalar_k(ROW_CLAIMS, &claims_bytes(claim, rhs2));
    let (current, r) = final_rounds(&mut t, certificate, claim.add(rhs2.mul_qm31(lambda)))?;
    mark(obs, Phase::QueryPart(5, 1));
    let (eq, digits) = equality_tables(&r);
    mark(obs, Phase::QueryPart(5, 2));
    let f_at = final_message_at(final_message, &eq)?;
    mark(obs, Phase::QueryPart(5, 3));
    let weights = Weights::new(p.variant, &p.semantic_alpha, &p.z)?;
    let w_at = weights.mle_at(&p.alpha[..2], p.kappa, &eq, &digits)?;
    mark(obs, Phase::QueryPart(5, 4));
    #[cfg(feature = "future-d-pair-expansion")]
    let q_at = query_weight_mle_pairs(p, geometry, &r)?;
    #[cfg(not(feature = "future-d-pair-expansion"))]
    let q_at = query_weight_mle(p, geometry, &r)?;
    mark(obs, Phase::QueryPart(5, 5));
    let combined = w_at.add(E::from_qm31(q_at.mul(lambda)));
    if f_at.mul(combined) != current {
        return Err(Error::Relation);
    }
    Ok(())
}

/// The six rounds of the final sumcheck: the running claim and the six challenges.
#[inline(always)]
fn final_rounds<H: Digest32>(t: &mut Transcript<H>, certificate: &[u8], start: E) -> Result<(E, [K; 6]), Error> {
    let mut current = start;
    let mut r = [K::ZERO; 6];
    for b in 0..6 {
        let bytes = &certificate[64 * b..64 * b + 64];
        let c0 = E::from_le_bytes(&bytes[..32]).ok_or(Error::Parse)?;
        let c2 = E::from_le_bytes(&bytes[32..]).ok_or(Error::Parse)?;
        r[b] = t.scalar_k(ROW_ROUND + b as u8, bytes);
        // s(0) + s(1) = 2 c0 + c1 + c2 is the running claim.
        let c1 = current.sub(c0).sub(c0).sub(c2);
        current = c0.add(c1.add(c2.mul_qm31(r[b])).mul_qm31(r[b]));
    }
    Ok((current, r))
}
#[inline(always)]
fn final_message_at(final_message: &[u8], eq: &[K; 64]) -> Result<E, Error> {
    let mut f_dot = EbyKDot::new();
    for j in 0..64 {
        match f_dot.push(field(final_message, j), eq[j]) { Ok(()) => {}, Err(_) => return Err(Error::Parse) }
    }
    Ok(f_dot.finish())
}

""")
# (f) merged_tree: read the key by value, so no operator on a reference is needed
t = sub(t, "    for key in keys {\n        let index = (key >> 8) as u32;", "    for &key in keys {\n        let index = (key >> 8) as u32;")
out[C + 'fused.rs'] = t

# ---------------------------------------------------------------- weights.rs
t = src(C + 'weights.rs')
old = cut(t, "    #[inline(never)]\n    pub fn mle_at(&self,alpha:&[E],kappa:E,eq:&[K;64],digits:&[[K;4];3])->Result<E,Error> {", "/// FUTURE-VERSION EXPERIMENT (profiling builds only): `Weights::pair`")
t = sub(t, old, """    fn row_product(&self,k:usize,digits:&[[K;4];3])->Result<K,Error> {
        let mut product=K::ONE;
        for d in 0..3 {
            let value=digit_dot(&digits[d],&self.factors[k][d+2])?;
            product=if d==0 {value} else {product.mul(value)};
        }
        Ok(product)
    }
    fn product_rows(&self,ap0:&[E;4],ap1:&[E;4],digits:&[[K;4];3],parts:&mut [E;7])->Result<(),Error> {
        const KINDS:[usize;5]=[1,2,3,5,6];
        for k in 0..5 {
            let product=self.row_product(k,digits)?;
            let scale=Self::scalar_factor(&self.factors[k][0],ap0).mul(Self::scalar_factor(&self.factors[k][1],ap1));
            parts[KINDS[k]]=scale.mul_qm31(product);
        }
        Ok(())
    }
    /// D1 (feature future-d-inactive-tensor): the inactive row through its tensor form.
    fn inactive_tensor(ap0:&[E;4],ap1:&[E;4],groups:&[K;12])->Result<E,Error> {
        let mut m=[K::ZERO;16];
        for g in 0..12 { for bit in 0..16 { if S2_INACTIVE_MASKS[g]&(1<<bit)!=0 {m[bit]=m[bit].add(groups[g]);} } }
        let mut total=E::ZERO;
        for b in 0..4 {
            let inner=perm_dot(ap0,&m,4*b)?;
            total=total.add(ap1[PERM[b]].mul(inner));
        }
        Ok(total.mul_m31(QUARTER.mul(QUARTER)))
    }
    #[inline(never)]
    pub fn mle_at(&self,alpha:&[E],kappa:E,eq:&[K;64],digits:&[[K;4];3])->Result<E,Error> {
        if self.variant!=Variant::S2||alpha.len()!=2 {return Err(Error::Parse);}
        let ap0=powers::<4>(alpha[0]);
        let ap1=powers::<4>(alpha[1]);
        let mut parts=[E::ZERO;7];
        self.product_rows(&ap0,&ap1,digits,&mut parts)?;
        let mut groups=[K::ZERO;12];
        for j in 0..64 { let g=S2_INACTIVE_GROUPS[j] as usize; groups[g]=groups[g].add(eq[j]); }
        parts[0]=Self::inactive_tensor(&ap0,&ap1,&groups)?;
        let libra=factored_s2_libra_weights(&ap0,&ap1,self.extra);
        parts[4]=libra_at(&libra,eq)?;
        let k=powers::<7>(kappa);let mut sum=E::ZERO;
        for kind in 0..7 {sum=sum.add(k[kind].mul(parts[kind]));}
        Ok(sum)
    }
}
fn digit_dot(digits:&[K;4],factors:&[K;4])->Result<K,Error> {
    let mut dot=crate::fast_pairing::KbyKDot::new();
    for m in 0..4 { match dot.push(digits[m],factors[m]) { Ok(()) => {}, Err(_) => return Err(Error::Parse) } }
    Ok(dot.finish())
}
fn perm_dot(ap:&[E;4],m:&[K;16],base:usize)->Result<E,Error> {
    let mut dot=crate::fast_pairing::EbyKDot::new();
    for a in 0..4 { match dot.push(ap[PERM[a]],m[a+base]) { Ok(()) => {}, Err(_) => return Err(Error::Parse) } }
    Ok(dot.finish())
}
fn libra_at(libra:&[E;4],eq:&[K;64])->Result<E,Error> {
    let mut dot=crate::fast_pairing::EbyKDot::new();
    for j in 0..4 { match dot.push(libra[j],eq[j]) { Ok(()) => {}, Err(_) => return Err(Error::Parse) } }
    Ok(dot.finish())
}

""")
out[C + 'weights.rs'] = t

# ---------------------------------------------------------------- multiproof.rs
t = src(C + 'multiproof.rs')
old = cut(t, "fn well_formed_merged(indices: &[u32]) -> bool {", "/// `node_count` for a binary tree and an index set of up to `MAX_MERGED`")
t = sub(t, old, """fn well_formed_merged(indices: &[u32]) -> bool {
    if indices.is_empty() || indices.len() > MAX_MERGED {
        return false;
    }
    let mut ok = indices[0] < 1 << LEAF_BITS;
    let mut i = 1;
    while i < indices.len() {
        ok = ok && indices[i - 1] < indices[i] && indices[i] < 1 << LEAF_BITS;
        i += 1;
    }
    ok
}

""")
old = cut(t, "    let mut other = [[0u8; 32]; MAX_MERGED];\n    let (mut cur, mut nxt): (&mut [[u8; 32]; MAX_MERGED], &mut [[u8; 32]; MAX_MERGED]) = (val, &mut other);", "/// Prover side: emit the canonical node sequence.")
t = sub(t, old, """    // Eighteen levels as nine pairs: `val` to `other`, then `other` back to `val`. The same digests in the
    // same order as exchanging two buffer references each level; the result is in `val`.
    let mut other = [[0u8; 32]; MAX_MERGED];
    let mut at = 0usize;
    let mut short = false;
    let mut pair = 0;
    while pair < 9 && !short {
        match merged_level(hash, idx, val, &mut other, n, slot, at) {
            None => short = true,
            Some((w, a)) => match merged_level(hash, idx, &other, val, w, slot, a) {
                None => short = true,
                Some((w2, a2)) => {
                    n = w2;
                    at = a2;
                }
            },
        }
        pair += 1;
    }
    if short {
        return Counted::Short;
    }
    Counted::Done { root_ok: n == 1 && idx[0] == 0 && val[0] == *root, used: at }
}

/// One level of the merged traversal, from `cur` into `nxt`: the new entry count and slot offset, or `None`
/// when the slot holds too few sibling nodes.
#[inline(always)]
fn merged_level<H: Digest32>(
    hash: H,
    idx: &mut [u32; MAX_MERGED],
    cur: &[[u8; 32]; MAX_MERGED],
    nxt: &mut [[u8; 32]; MAX_MERGED],
    n: usize,
    slot: &[u8],
    mut at: usize,
) -> Option<(usize, usize)> {
    let tag = [BINARY_NODE_TAG];
    let mut w = 0;
    let mut i = 0;
    while i < n {
        let index = idx[i];
        if i + 1 < n && idx[i + 1] == index ^ 1 {
            hash.digest_into(&[&tag, &cur[i], &cur[i + 1]], &mut nxt[w]);
            i += 2;
        } else {
            let Some(sibling) = slot.get(at..at + 32) else { return None };
            at += 32;
            if index & 1 == 0 {
                hash.digest_into(&[&tag, &cur[i], sibling], &mut nxt[w]);
            } else {
                hash.digest_into(&[&tag, sibling, &cur[i]], &mut nxt[w]);
            }
            i += 1;
        }
        idx[w] = index >> 1;
        w += 1;
    }
    Some((w, at))
}

""")
out[C + 'multiproof.rs'] = t

# ---------------------------------------------------------------- r1_wire.rs
t = src(C + 'r1_wire.rs')
t = sub(t, """        #[cfg(feature = "future-validated-decode")]
        for (value, part) in bytes.chunks_exact(32).enumerate() {
            let limb = |at: usize| aspis_core::field::M31(u32::from_le_bytes([part[at], part[at + 1], part[at + 2], part[at + 3]]));
            out[value] = QM31 {
                c0: aspis_core::field::CM31 { a: limb(0), b: limb(4) },
                c1: aspis_core::field::CM31 { a: limb(8), b: limb(12) },
            };
        }
""", """        #[cfg(feature = "future-validated-decode")]
        {
            let mut value = 0;
            while value < N {
                let part = &bytes[32 * value..32 * value + 32];
                let limb = |at: usize| aspis_core::field::M31(u32::from_le_bytes([part[at], part[at + 1], part[at + 2], part[at + 3]]));
                out[value] = QM31 {
                    c0: aspis_core::field::CM31 { a: limb(0), b: limb(4) },
                    c1: aspis_core::field::CM31 { a: limb(8), b: limb(12) },
                };
                value += 1;
            }
        }
""")
out[C + 'r1_wire.rs'] = t

# ---------------------------------------------------------------- r1_semantic.rs
t = src(C + 'r1_semantic.rs')
t = sub(t, """        let value = polynomial
            .iter()
            .rev()
            .fold(QM31::ZERO, |a, &c| a.mul_add(alpha[round], c));
    value
""", """        let mut value = QM31::ZERO;
        let mut i = 28;
        while i > 0 {
            i -= 1;
            value = value.mul_add(alpha[round], polynomial[i]);
        }
    value
""")
out[C + 'r1_semantic.rs'] = t


# ================================================================ second round (after run XP-A10)
# (g) relation_view: the three empty slices come from a named constant. With `--mir built` a literal `&[]` is a borrow
#     of a temporary of this function, and returning it inside the struct is rejected ("no bottoms in the value").
t = out[C + 'fused.rs']
t = sub(t, "fn relation_view(proof: &[u8]) -> Result<View<'_>, Error> {\n", "const NO_BYTES: &[u8] = &[];\nfn relation_view(proof: &[u8]) -> Result<View<'_>, Error> {\n")
t = sub(t, """        variant: Variant::S2,
        semantic: &[],
        y1: &[],
        inactive,
        round0: &proof[compact::OFF_ROUND0..compact::OFF_FOLDED_ROOT],
        folded_root: None,
        round1: &proof[compact::OFF_ROUND1..compact::OFF_FINAL],
        final_message: &proof[compact::OFF_FINAL..compact::OFF_OPENINGS],
        query_bytes: &[],""", """        variant: Variant::S2,
        semantic: NO_BYTES,
        y1: NO_BYTES,
        inactive,
        round0: &proof[compact::OFF_ROUND0..compact::OFF_FOLDED_ROOT],
        folded_root: None,
        round1: &proof[compact::OFF_ROUND1..compact::OFF_FINAL],
        final_message: &proof[compact::OFF_FINAL..compact::OFF_OPENINGS],
        query_bytes: NO_BYTES,""")
# (h) arrays of accumulators are read by index through a by-reference `value`, not moved out with `let [a, b, c, d] = dots`
t = sub(t, """        push_k4(&mut dots, &circle[i], &signed)?;
    }
    let [d0, d1, d2, d3] = dots;
    Ok([d0.finish(), d1.finish(), d2.finish(), d3.finish()])
}
""", """        push_k4(&mut dots, &circle[i], &signed)?;
    }
    Ok([dots[0].value(), dots[1].value(), dots[2].value(), dots[3].value()])
}
""")
t = sub(t, """fn finish_e4(dots: [EbyKDot; 4]) -> [E; 4] {
    let [d0, d1, d2, d3] = dots;
    [d0.finish(), d1.finish(), d2.finish(), d3.finish()]
}""", """fn finish_e4(dots: &[EbyKDot; 4]) -> [E; 4] {
    [dots[0].value(), dots[1].value(), dots[2].value(), dots[3].value()]
}""")
t = sub(t, "    let lhs1 = cubic(alpha[0], finish_e4(first));", "    let lhs1 = cubic(alpha[0], finish_e4(&first));")
t = sub(t, "    let rhs2 = cubic(alpha[1], finish_e4(second));", "    let rhs2 = cubic(alpha[1], finish_e4(&second));")
out[C + 'fused.rs'] = t
t = src(C + 'fast_pairing.rs')
t = sub(t, "        pub fn finish(self)->Q {Q([reduce(self.sums[0]),reduce(self.sums[1]),reduce(self.sums[2]),reduce(self.sums[3])])}\n",
        "        pub fn finish(self)->Q {Q([reduce(self.sums[0]),reduce(self.sums[1]),reduce(self.sums[2]),reduce(self.sums[3])])}\n"
        "        /// `finish` without consuming the accumulator (same value).\n"
        "        pub fn value(&self)->Q {Q([reduce(self.sums[0]),reduce(self.sums[1]),reduce(self.sums[2]),reduce(self.sums[3])])}\n")
t = sub(t, """        // The private accumulator produces canonical coordinates already.
        E::from_limbs([a,b,c,d,e,f,g,h]).unwrap()
    }
}
""", """        // The private accumulator produces canonical coordinates already.
        E::from_limbs([a,b,c,d,e,f,g,h]).unwrap()
    }

    /// `finish` without consuming the accumulator (same value).
    #[inline(always)]
    pub fn value(&self) -> E {
        let [a,b,c,d]=self.c0.value().limbs();
        let [e,f,g,h]=self.c1.value().limbs();
        E::from_limbs([a,b,c,d,e,f,g,h]).unwrap()
    }
}
""")
t = sub(t, """    pub fn finish(self) -> QM31 {
        qm31_of(self.dot.finish())
    }
}
""", """    pub fn finish(self) -> QM31 {
        qm31_of(self.dot.finish())
    }

    /// `finish` without consuming the accumulator (same value).
    #[inline(always)]
    pub fn value(&self) -> QM31 {
        qm31_of(self.dot.value())
    }
}
""")
out[C + 'fast_pairing.rs'] = t
# (i) decode_k: no closure inside the loop (a closure holding a borrow is what the loop join rejects)
t = out[C + 'r1_wire.rs']
t = sub(t, """                let limb = |at: usize| aspis_core::field::M31(u32::from_le_bytes([part[at], part[at + 1], part[at + 2], part[at + 3]]));
                out[value] = QM31 {
                    c0: aspis_core::field::CM31 { a: limb(0), b: limb(4) },
                    c1: aspis_core::field::CM31 { a: limb(8), b: limb(12) },
                };
                value += 1;""", """                out[value] = QM31 {
                    c0: aspis_core::field::CM31 { a: validated_limb(part, 0), b: validated_limb(part, 4) },
                    c1: aspis_core::field::CM31 { a: validated_limb(part, 8), b: validated_limb(part, 12) },
                };
                value += 1;""")
t = sub(t, "/// A record whose framing and every field limb were checked by\n", "#[inline(always)]\nfn validated_limb(part: &[u8], at: usize) -> aspis_core::field::M31 {\n    aspis_core::field::M31(u32::from_le_bytes([part[at], part[at + 1], part[at + 2], part[at + 3]]))\n}\n\n/// A record whose framing and every field limb were checked by\n")
out[C + 'r1_wire.rs'] = t


# ================================================================ third round (after run XP-A11)
# (j) decode_k: the loop moves to a function that sees only the byte slice. Inside decode_k, `&self` is a shared borrow
#     of a record that itself holds a borrow, and a loop in that scope is what the join rejects (the R1 form fails the same way).
t = out[C + 'r1_wire.rs']
old = cut(t, """        #[cfg(feature = "future-validated-decode")]
        {
            let mut value = 0;""", """        #[cfg(not(feature = "future-validated-decode"))]""")
t = sub(t, old, """        #[cfg(feature = "future-validated-decode")]
        {
            out = validated_values::<N>(bytes);
        }
""")
t = sub(t, "#[inline(always)]\nfn validated_limb(part: &[u8], at: usize) -> aspis_core::field::M31 {", """/// E3: load `N` already-validated QM31 values (32 bytes each, low 16 used) from `bytes`.
#[inline(always)]
fn validated_values<const N: usize>(bytes: &[u8]) -> [QM31; N] {
    let mut out = [QM31::ZERO; N];
    let mut value = 0;
    while value < N {
        let part = &bytes[32 * value..32 * value + 32];
        out[value] = QM31 {
            c0: aspis_core::field::CM31 { a: validated_limb(part, 0), b: validated_limb(part, 4) },
            c1: aspis_core::field::CM31 { a: validated_limb(part, 8), b: validated_limb(part, 12) },
        };
        value += 1;
    }
    out
}
#[inline(always)]
fn validated_limb(part: &[u8], at: usize) -> aspis_core::field::M31 {""")
out[C + 'r1_wire.rs'] = t
# (k) mle_at: its two remaining loops move to small functions, so the body has no loop
t = out[C + 'weights.rs']
t = sub(t, """        let mut groups=[K::ZERO;12];
        for j in 0..64 { let g=S2_INACTIVE_GROUPS[j] as usize; groups[g]=groups[g].add(eq[j]); }
        parts[0]=Self::inactive_tensor(&ap0,&ap1,&groups)?;
        let libra=factored_s2_libra_weights(&ap0,&ap1,self.extra);
        parts[4]=libra_at(&libra,eq)?;
        let k=powers::<7>(kappa);let mut sum=E::ZERO;
        for kind in 0..7 {sum=sum.add(k[kind].mul(parts[kind]));}
        Ok(sum)
    }
}
""", """        let groups=inactive_groups(eq);
        parts[0]=Self::inactive_tensor(&ap0,&ap1,&groups)?;
        let libra=factored_s2_libra_weights(&ap0,&ap1,self.extra);
        parts[4]=libra_at(&libra,eq)?;
        Ok(kappa_sum(kappa,&parts))
    }
}
fn inactive_groups(eq:&[K;64])->[K;12] {
    let mut groups=[K::ZERO;12];
    for j in 0..64 { let g=S2_INACTIVE_GROUPS[j] as usize; groups[g]=groups[g].add(eq[j]); }
    groups
}
fn kappa_sum(kappa:E,parts:&[E;7])->E {
    let k=powers::<7>(kappa);let mut sum=E::ZERO;
    for kind in 0..7 {sum=sum.add(k[kind].mul(parts[kind]));}
    sum
}
""")
out[C + 'weights.rs'] = t

for p, text in out.items():
    q = OUT / p; q.parent.mkdir(parents=True, exist_ok=True); q.write_text(text)
    print(p, len(text))
