#!/usr/bin/env python3
"""Aspis translatability pass, patch 1: rewrites for the translator on top of patch 0.
Reads a tree (base + patch 0) from a directory and writes the changed files to an output directory.
Every replaced text must occur exactly once. usage: TP_rewrite_p1.py <tree dir> <out dir>"""
import re, sys
from pathlib import Path
T, OUT = Path(sys.argv[1]), Path(sys.argv[2])
C = 'crates/aspis-r1-cost-probe/'; P = 'programs/r1-cost-probe/'
def sub(t, old, new, n=1):
    assert t.count(old) == n, ('count', old[:90], t.count(old)); return t.replace(old, new)
def rsub(t, pat, new):
    m = list(re.finditer(pat, t, re.S)); assert len(m) == 1, ('regex count', pat[:70], len(m)); return t[:m[0].start()] + new + t[m[0].end():]
def fn_text(t, head):
    """text of the function whose signature starts with `head` (to its closing brace at the indentation of the head)"""
    i = t.index(head); ind = re.search(r'[ \t]*$', t[:i]).group(0)
    j = t.index('\n' + ind + '}\n', i) + len('\n' + ind + '}')
    return t[i:j]
out = {}

# ------------------------------------------------------------------ verifier.rs
f = C + 'src/verifier.rs'; t = (T / f).read_text()
# Patch 0 (third version) leaves `prepared_claim` as the base tree has it (one definition with `if cfg!` inside). The
# first step here is therefore its split into the pinned text under `#[cfg(not(feature="future-claim-rows"))]` and the
# claim-rows variant under `#[cfg(feature="future-claim-rows")]` (TP_restore.py in mode `claim`, which reads the pinned
# text with `git show`: run this script from the repository root).
if 'if cfg!(feature="future-claim-rows")' in t:
    import subprocess, tempfile
    with tempfile.TemporaryDirectory() as tmp:
        subprocess.check_call([sys.executable, '-I', str(Path(__file__).with_name('TP_restore.py')), str(T), tmp, 'claim'], stdout=subprocess.DEVNULL)
        t = (Path(tmp) / f).read_text()
# prepared_claim: the text of research evidence lean-candidates/s1-claim-fission-sum-proved-candidate-20261020/claim-fission.patch,
# verbatim (helper names, bodies, order; the file is in the main checkout's docs/research tree, sha256
# b550885634d8abc0ffd19cce5bd89be2894b06fbcb62e1aa41f87ab137edeb9b). Only the cfg attribute is added. No inlining
# attribute: forcing the helpers inline costs 1,031 compute units more, and not inlining the dot about 1,900 more
# (bisect run b3).
old = fn_text(t, 'fn prepared_claim<H:Digest32>(sem:&crate::r1_semantic::Verified<H>,y1:&[u8],inactive:E,g:&[E;29],kappa:E)->Result<E,Error> {\n        let k=powers::<7>(kappa);\n        let mut parts=[E::ZERO;7];parts[0]=inactive;\n        for point in 0..6 {\n            let mut dot')
t = sub(t, '#[cfg(not(feature="future-claim-rows"))]\n' + old, '''#[cfg(not(feature="future-claim-rows"))]
fn prepared_claim_sum(k:[E;7],parts:[E;7])->E {
        let mut claim=E::ZERO;
        for i in 0..7 {crate::trace::value(14,i,parts[i]);claim=claim.add(k[i].mul(parts[i]));}
        crate::trace::value(14,7,claim);
        claim
}
#[cfg(not(feature="future-claim-rows"))]
fn prepared_claim_dot<H:Digest32>(sem:&crate::r1_semantic::Verified<H>,y1:&[u8],g:&[E;29],point:usize)->Result<E,Error> {
    let mut dot=crate::fast_pairing::EbyKDot::new();
    for l in 0..29 {
        let scalar=match point {0..=2=>sem.claims[point][l],3=>sem.extra[l],4=>sem.before_z1[l],_=>field(y1,l).c0()};
        dot.push(g[l],scalar).map_err(|_|Error::Parse)?;
    }
    Ok(dot.finish())
}
#[cfg(not(feature="future-claim-rows"))]
fn prepared_claim<H:Digest32>(sem:&crate::r1_semantic::Verified<H>,y1:&[u8],inactive:E,g:&[E;29],kappa:E)->Result<E,Error> {
        let k=powers::<7>(kappa);
        let mut parts=[E::ZERO;7];parts[0]=inactive;
        for point in 0..6 {
            parts[point+1]=prepared_claim_dot(sem,y1,g,point)?;
        }
        Ok(prepared_claim_sum(k,parts))
}''')
# Prepared::new: the second folding challenge in its own function; no tuple-valued `if`
t = sub(t, '''        let (alpha,row)=if v.variant.folds()==2 {
            let mut bytes=Vec::with_capacity(32+224);bytes.extend_from_slice(v.folded_root.unwrap());bytes.extend_from_slice(v.round1);
            ([alpha0,t.scalar(30,&bytes,false)],31)
        } else {
            ([alpha0,E::ZERO],30)
        };
''', '''        let alpha=[alpha0,second_alpha(&mut t,v)];
        let row:u8=if v.variant.folds()==2 {31} else {30};
''')
t = sub(t, 'impl Prepared {\n    #[inline(never)]\n    pub fn new<H:Digest32>', '''/// The second folding challenge: with two folds, row 30 over the folded root followed by the second round
/// message; with one fold, zero and no transcript row.
#[inline(never)]
fn second_alpha<H:Digest32>(t:&mut Transcript<H>,v:&View<'_>)->E {
    if v.variant.folds()==2 {
        let mut bytes=Vec::with_capacity(32+224);bytes.extend_from_slice(v.folded_root.unwrap());bytes.extend_from_slice(v.round1);
        t.scalar(30,&bytes,false)
    } else {
        E::ZERO
    }
}
impl Prepared {
    #[inline(never)]
    pub fn new<H:Digest32>''')
out[f] = t

# ------------------------------------------------------------------ r1_semantic.rs
f = C + 'src/r1_semantic.rs'; t = (T / f).read_text()
# semantic_boundary, Aspis form (new gate): index loop, reductions called directly
old = fn_text(t, 'fn semantic_boundary(polynomial: &[QM31; 28]) -> QM31 {\n    // FUTURE-VERSION EXPERIMENT E8')
t = sub(t, old, '''fn semantic_boundary(polynomial: &[QM31; 28]) -> QM31 {
    // FUTURE-VERSION EXPERIMENT E8 (default off): the same sum
    // `p[0] + (p[0] + ... + p[27])` with one reduction per limb. The 29
    // canonical limbs sum below 2^36.
    use aspis_core::field::{CM31, M31};
    let first = polynomial[0];
    let mut sums = [u64::from(first.c0.a.0), u64::from(first.c0.b.0), u64::from(first.c1.a.0), u64::from(first.c1.b.0)];
    let mut i = 0;
    while i < 28 {
        let c = &polynomial[i];
        sums[0] += u64::from(c.c0.a.0);
        sums[1] += u64::from(c.c0.b.0);
        sums[2] += u64::from(c.c1.a.0);
        sums[3] += u64::from(c.c1.b.0);
        i += 1;
    }
    QM31 {
        c0: CM31 { a: M31::reduce_u64(sums[0]), b: M31::reduce_u64(sums[1]) },
        c1: CM31 { a: M31::reduce_u64(sums[2]), b: M31::reduce_u64(sums[3]) },
    }
}''')
# Aspis entries without the observer (new gate): verify_observed and verify_finish with the parameter and the marks removed
vf = fn_text(t, 'fn verify_finish<H: Digest32>(')
core = vf.replace('fn verify_finish<H: Digest32>(', 'fn verify_finish_unobserved<H: Digest32>(', 1)
core = sub(core, ', challenges: Challenges, obs: crate::verifier::Observer) -> Result<Verified<H>, Error> {', ', challenges: Challenges) -> Result<Verified<H>, Error> {')
n_marks = len(re.findall(r'(?m)^[ \t]*mark\(obs, \d\);\n', core)); assert n_marks == 4, n_marks
core = re.sub(r'(?m)^[ \t]*mark\(obs, \d\);\n', '', core); assert not re.search(r'\bobs\b', core)
vo = fn_text(t, 'pub fn verify_observed<H: Digest32>(')
t = sub(t, vo, vo + '''

/// Aspis entry (new gate): `verify_observed` without the observer parameter. The same calls in the same
/// order; the shared functions (`Prefix::parse`, `public_transcript`, `begin`) are called unchanged.
#[inline(never)]
pub fn verify_unobserved<H: Digest32>(public: Public<'_>, bytes: &[u8], hash: H) -> Result<Verified<H>, Error> {
    let prefix = Prefix::parse(bytes)?;
    let mut transcript = public_transcript(public, hash, prefix.c1_root)?;
    let challenges = wire::begin(&prefix, &mut transcript)?;
    verify_finish_unobserved(public, prefix, transcript, challenges)
}

/// Aspis form of `verify_finish` (new gate): the same body without the observer parameter and its four marks.
#[inline(never)]
''' + core)
out[f] = t

# ------------------------------------------------------------------ fast_pairing.rs
f = C + 'src/fast_pairing.rs'; t = (T / f).read_text()
old = fn_text(t, 'pub fn push(&mut self, left: QM31, right: QM31) -> Result<(), ()> {')
assert 'if cfg!(feature = "future-lean-dot")' in old
new_checked = old.replace('''        if cfg!(feature = "future-lean-dot") {
            self.push_lean(left, right);
            return Ok(());
        }
''', '')
assert new_checked != old
t = sub(t, '    #[inline(always)]\n    ' + old, '    #[cfg(not(feature = "future-lean-dot"))]\n    #[inline(always)]\n    ' + new_checked + '''

    #[cfg(feature = "future-lean-dot")]
    #[inline(always)]
    pub fn push(&mut self, left: QM31, right: QM31) -> Result<(), ()> {
        self.push_lean(left, right);
        Ok(())
    }''')
out[f] = t

# ------------------------------------------------------------------ fused.rs
f = C + 'src/fused.rs'; t = (T / f).read_text()
t = sub(t, 'use crate::transcript::Transcript;\n', '''use crate::transcript::Transcript;

/// Profiling hook of the one-transaction functions. With `phase-observer` it carries the observer; without it
/// (every deployed build) it is a zero-sized value, so no function-pointer type is on the on-chain path.
#[cfg(feature = "phase-observer")]
#[derive(Clone, Copy)]
pub(crate) struct Hook(Observer);
#[cfg(not(feature = "phase-observer"))]
#[derive(Clone, Copy)]
pub(crate) struct Hook;
impl Hook {
    #[cfg(feature = "phase-observer")]
    pub(crate) const NONE: Hook = Hook(None);
    #[cfg(not(feature = "phase-observer"))]
    pub(crate) const NONE: Hook = Hook;
    /// From an observer. Without `phase-observer` the observer is dropped.
    #[cfg(feature = "phase-observer")]
    #[inline(always)]
    pub(crate) fn of(obs: Observer) -> Self {
        Hook(obs)
    }
    #[cfg(not(feature = "phase-observer"))]
    #[inline(always)]
    pub(crate) fn of(obs: Observer) -> Self {
        let _ = obs;
        Hook
    }
    #[cfg(feature = "phase-observer")]
    #[inline(always)]
    fn note(self, phase: Phase) {
        mark(self.0, phase)
    }
    #[cfg(not(feature = "phase-observer"))]
    #[inline(always)]
    fn note(self, phase: Phase) {
        let _ = phase;
    }
}
''')
# fold_sums and summed_final_checks take the hook
for head in ('fn fold_sums(', 'fn summed_final_checks<H: Digest32>('):
    old = fn_text(t, head)
    new = sub(old, 'obs: Observer) -> Result<', 'hook: Hook) -> Result<').replace('mark(obs, ', 'hook.note(')
    assert not re.search(r'\bobs\b', new), head
    t = sub(t, old, new)
# the entry: body under a hook; two thin entries
old = fn_text(t, 'pub fn verify_summed_format<H: Digest32>(')
body = old.replace('pub fn verify_summed_format<H: Digest32>(public: Public<\'_>, proof: &[u8], hash: H, obs: Observer)', 'fn verify_summed_format_hooked<H: Digest32>(public: Public<\'_>, proof: &[u8], hash: H, hook: Hook)', 1)
body = sub(body, 'let p = prepare(public, proof, hash, obs, &mut g)?;', 'let p = prepare_summed(public, proof, hash, hook, &mut g)?;')
body = body.replace('mark(obs, ', 'hook.note(').replace(', obs)?;', ', hook)?;')
assert not re.search(r'\bobs\b', body)
t = sub(t, old, body + '''

/// The entry with an observer, as before (tests, tools, profiling builds). Without `phase-observer` the
/// observer is ignored.
#[inline(always)]
pub fn verify_summed_format<H: Digest32>(public: Public<'_>, proof: &[u8], hash: H, obs: Observer) -> Result<(), Error> {
    verify_summed_format_hooked(public, proof, hash, Hook::of(obs))
}

/// The on-chain entry of the Aspis one-transaction verifier: no observer parameter.
#[inline(always)]
pub fn verify_summed_format_unobserved<H: Digest32>(public: Public<'_>, proof: &[u8], hash: H) -> Result<(), Error> {
    verify_summed_format_hooked(public, proof, hash, Hook::NONE)
}

/// `candidate::prepare` for the one-transaction path (new gate): the same steps in the same order, with the
/// semantic layer entered through `verify_unobserved` unless a profiling build asks for the observer.
#[inline(never)]
fn prepare_summed<H: Digest32>(public: Public<'_>, proof: &[u8], hash: H, hook: Hook, g: &mut [E; 29]) -> Result<Box<Prepared>, Error> {
    let mut logical = aspis_core::r0::heap::filled(compact::LOGICAL_SEMANTIC + compact::LOGICAL_Y1, 0u8).map_err(|_| Error::Allocation)?;
    let (semantic, y1) = logical.split_at_mut(compact::LOGICAL_SEMANTIC);
    compact::expand_semantic(&proof[compact::OFF_SEMANTIC..compact::OFF_Y1], semantic)?;
    compact::expand_values(&proof[compact::OFF_Y1..compact::OFF_INACTIVE], y1)?;
    let v = wide_view(proof, &logical[..compact::LOGICAL_SEMANTIC], &logical[compact::LOGICAL_SEMANTIC..])?;
    #[cfg(feature = "phase-observer")]
    let sem = crate::r1_semantic::verify_observed(public, v.semantic, hash, hook.0).map_err(|_| Error::Semantic)?;
    #[cfg(not(feature = "phase-observer"))]
    let sem = crate::r1_semantic::verify_unobserved(public, v.semantic, hash).map_err(|_| Error::Semantic)?;
    hook.note(Phase::Semantic);
    Prepared::new(&sem, &v, hash, g)
}''')
# every other caller of the two inner functions passes a hook
n1 = t.count('&geometry, obs)?;'); t = t.replace('&geometry, obs)?;', '&geometry, Hook::of(obs))?;')
n2 = t.count('certificate, hash, obs)?;'); t = t.replace('certificate, hash, obs)?;', 'certificate, hash, Hook::of(obs))?;')
n3 = t.count('&geometry, None)?;'); t = t.replace('&geometry, None)?;', '&geometry, Hook::NONE)?;')
# the unit tests of this file call the two functions with no observer: twelve call sites
t, n4 = re.subn(r'(fold_sums\([^;\n]*?&geometry), None\)', r'\1, Hook::NONE)', t)
t, n5 = re.subn(r'(summed_final_checks\([^;\n]*?, Sha), None\)', r'\1, Hook::NONE)', t)
assert (n4, n5) == (6, 6), (n4, n5)
print('fused.rs callers updated:', n1, n2, n3)
# coefficients: the feature choice by #[cfg]
t = rsub(t, r'        line\[i\] = if cfg!\(feature = "future-fold-shared"\) \{\n.*?\n        \};\n', '''        #[cfg(feature = "future-fold-shared")]
        {
            // G6 uses only the first and fourth entries.
            let _ = (lx, ly);
            line[i] = [r, K::ZERO, K::ZERO, rz, K::ZERO, K::ZERO];
        }
        #[cfg(not(feature = "future-fold-shared"))]
        {
            line[i] = [r, r.mul_m31(lx), r.mul_m31(ly), rz, rz.mul_m31(lx), rz.mul_m31(ly).neg()];
        }
''')
# k_of: the four reductions called directly (no function passed as a value)
t = sub(t, '''fn k_of(limbs: [u64; 4]) -> K {
    let [a, b, c, d] = limbs.map(M31::reduce_u64);
    K { c0: aspis_core::field::CM31 { a, b }, c1: aspis_core::field::CM31 { a: c, b: d } }
}''', '''fn k_of(limbs: [u64; 4]) -> K {
    K {
        c0: aspis_core::field::CM31 { a: M31::reduce_u64(limbs[0]), b: M31::reduce_u64(limbs[1]) },
        c1: aspis_core::field::CM31 { a: M31::reduce_u64(limbs[2]), b: M31::reduce_u64(limbs[3]) },
    }
}''')
# base_lanes_tight: the conversion of the mutable slice to a mutable array reference went through `map_err` and `?`.
# The tools translate that, but the emitted Lean applies the library's `map_err` and `branch` as if they returned a pair
# with a write-back function, which no library has (neither R1's nor the second pair's own). A `match` instead.
t = sub(t, '''        let acc: &mut [u64; 416] = (&mut acc[..]).try_into().map_err(|_| Error::Allocation)?;
''', '''        let acc: &mut [u64; 416] = match (&mut acc[..]).try_into() {
            Ok(array) => array,
            Err(_) => return Err(Error::Allocation),
        };
''')
out[f] = t

# ------------------------------------------------------------------ Cargo features
f = C + 'Cargo.toml'; t = (T / f).read_text()
t = sub(t, 'detail-phases = []\n', '# The observer (a function pointer) is carried by the one-transaction functions only with this feature.\nphase-observer = []\ndetail-phases = ["phase-observer"]\n')
out[f] = t
f = P + 'Cargo.toml'; t = (T / f).read_text()
t = sub(t, 'cu-profiling = []\n', 'cu-profiling = ["aspis-r1-cost-probe/phase-observer"]\n')
out[f] = t

# ------------------------------------------------------------------ program adapter
f = P + 'src/r1_pool_adapter_owned.rs'; t = (T / f).read_text()
# require_distinct_accounts keeps its pinned text (it serves the three-account call of `stage1_owned`, which the
# one-transaction entry does not reach). The tools reject it in any loop form: with the early return ("Returns inside
# of nested loops"), and with a flag in place of the return ("Found a case of unsupported nested borrows": the loop
# runs over an array of references). For the seven accounts of the ASQ8 instruction the same 21 comparisons are written
# out, in the order the loops make them (previous < index, index ascending), with the same error at the first equal pair.
t = sub(t, 'fn require_zero(mut remaining: &[u8]) -> ProgramResult {', '''/// `require_distinct_accounts` for the seven accounts of the ASQ8 instruction, written out: the same 21 key
/// comparisons in the same order, the same error at the first equal pair.
fn require_distinct_seven(a: &[&OwnedAccount; 7]) -> ProgramResult {
    if a[0].key() == a[1].key() {
        return Err(ProgramError::InvalidArgument);
    }
    if a[0].key() == a[2].key() {
        return Err(ProgramError::InvalidArgument);
    }
    if a[1].key() == a[2].key() {
        return Err(ProgramError::InvalidArgument);
    }
    if a[0].key() == a[3].key() {
        return Err(ProgramError::InvalidArgument);
    }
    if a[1].key() == a[3].key() {
        return Err(ProgramError::InvalidArgument);
    }
    if a[2].key() == a[3].key() {
        return Err(ProgramError::InvalidArgument);
    }
    if a[0].key() == a[4].key() {
        return Err(ProgramError::InvalidArgument);
    }
    if a[1].key() == a[4].key() {
        return Err(ProgramError::InvalidArgument);
    }
    if a[2].key() == a[4].key() {
        return Err(ProgramError::InvalidArgument);
    }
    if a[3].key() == a[4].key() {
        return Err(ProgramError::InvalidArgument);
    }
    if a[0].key() == a[5].key() {
        return Err(ProgramError::InvalidArgument);
    }
    if a[1].key() == a[5].key() {
        return Err(ProgramError::InvalidArgument);
    }
    if a[2].key() == a[5].key() {
        return Err(ProgramError::InvalidArgument);
    }
    if a[3].key() == a[5].key() {
        return Err(ProgramError::InvalidArgument);
    }
    if a[4].key() == a[5].key() {
        return Err(ProgramError::InvalidArgument);
    }
    if a[0].key() == a[6].key() {
        return Err(ProgramError::InvalidArgument);
    }
    if a[1].key() == a[6].key() {
        return Err(ProgramError::InvalidArgument);
    }
    if a[2].key() == a[6].key() {
        return Err(ProgramError::InvalidArgument);
    }
    if a[3].key() == a[6].key() {
        return Err(ProgramError::InvalidArgument);
    }
    if a[4].key() == a[6].key() {
        return Err(ProgramError::InvalidArgument);
    }
    if a[5].key() == a[6].key() {
        return Err(ProgramError::InvalidArgument);
    }
    Ok(())
}
fn require_zero(mut remaining: &[u8]) -> ProgramResult {''')
t = sub(t, '''    require_distinct_accounts(&[
        proof_account,
        master_account,
''', '''    require_distinct_seven(&[
        proof_account,
        master_account,
''')
t = sub(t, '''    let [proof_account, master_account, checkpoint_account, lane_account, registry_account, entry_account, verifier_checkpoint] =
        accounts
    else {
        return Err(if accounts.len() < 7 {
            ProgramError::NotEnoughAccountKeys
        } else {
            ProgramError::InvalidArgument
        });
    };
''', '''    if accounts.len() != 7 {
        return Err(if accounts.len() < 7 {
            ProgramError::NotEnoughAccountKeys
        } else {
            ProgramError::InvalidArgument
        });
    }
    let proof_account = &accounts[0];
    let master_account = &accounts[1];
    let checkpoint_account = &accounts[2];
    let lane_account = &accounts[3];
    let registry_account = &accounts[4];
    let entry_account = &accounts[5];
    let verifier_checkpoint = &accounts[6];
''')
t = sub(t, '''        verifier::candidate::fused::verify_summed_format(
            validated.statement.semantic_public(),
            &proof_data[proof_start..proof_end],
            super::super::SolanaDigest,
            super::super::observer(),
        )
        .map_err(super::super::error)?;
''', '''        #[cfg(feature = "cu-profiling")]
        verifier::candidate::fused::verify_summed_format(
            validated.statement.semantic_public(),
            &proof_data[proof_start..proof_end],
            super::super::SolanaDigest,
            super::super::observer(),
        )
        .map_err(super::super::error)?;
        #[cfg(not(feature = "cu-profiling"))]
        verifier::candidate::fused::verify_summed_format_unobserved(
            validated.statement.semantic_public(),
            &proof_data[proof_start..proof_end],
            super::super::SolanaDigest,
        )
        .map_err(super::super::error)?;
''')
out[f] = t
f = P + 'src/r1_pool_adapter.rs'; t = (T / f).read_text()
# The frontier loop. Forms that went through the tools (the fourth is the patch; `LANE=flag` as a fourth argument of
# this script gives the third):
#  1 counting loop with a flag inside the decoder, a `match` on the decode and an `if` that compares with the table of
#    empty roots in one branch only: rejected at the `if` ("Could not match the contexts");
#  2 the two checks of one level in a helper returning `Result<_, ProgramError>`, a `match` in the decoder's loop that
#    stores the node or sets the flag: rejected at the `match` (same message);
#  3 (`flag`) a helper returning a flag and the node, a loop body with no branch, still inside the decoder: 506 compute
#    units more than form 2 on the recorded payments (bisect run b5);
#  4 (`own`, the patch) form 2's loop moved into a function of its own, `lane_frontier`, as was done for the backward
#    pass of `for_range`: the decoder then has no loop.
# In every form each failure is `InvalidAccountData`, as in the pinned loop, and the frontier is not used when an error
# is returned, so the result is the same on every input. The shift amount is written `level as u32` (level is below
# 20): the R1 Lean library has the shift of a u64 by a u32 only, and the emitted Lean of `>> level` with a usize did
# not elaborate.
LANE = sys.argv[3] if len(sys.argv) > 3 else 'own'
assert LANE in ('own', 'flag')
LOOP = r'    for \(level, node\) in frontier\.iter_mut\(\)\.enumerate\(\) \{\n        let start = 48 \+ 32 \* level;\n.*?\n    \}\n(?=    if next_leaf_index == 0)'
DOC = '/// Exact source-release lane decoder copied from the ASQ8 audit path. It\n'
if LANE == 'flag':
    t = rsub(t, LOOP, """    let mut frontier_ok = true;
    let mut level = 0;
    while level < POOL_V1_PAIR_TREE_DEPTH {
        let (acceptable, node) = lane_frontier_node(tree, level, next_leaf_index);
        frontier[level] = node;
        frontier_ok &= acceptable;
        level += 1;
    }
    if !frontier_ok {
        return Err(ProgramError::InvalidAccountData);
    }
""")
    # The helper goes BEFORE the doc comment and `#[inline(never)]` of the decoder, so that both stay on the decoder.
    t = sub(t, DOC, """/// One frontier node of the lane account image (level `level`): whether it is acceptable (canonical, and equal to
/// the pinned empty root where the subtree is unoccupied, that is where bit `level` of the next leaf index is 0), and
/// the node (zero when it is not canonical).
#[inline(always)]
fn lane_frontier_node(tree: &[u8], level: usize, next_leaf_index: u64) -> (bool, [M31; 8]) {
    use v7_pair_empty_roots::V7_PAIR_EMPTY_ROOTS;
    let start = 48 + 32 * level;
    let bytes: [u8; 32] = match tree[start..start + 32].try_into() {
        Ok(bytes) => bytes,
        Err(_) => return (false, [M31::ZERO; 8]),
    };
    match decode_digest_canonical(&bytes) {
        Ok(node) => {
            if (next_leaf_index >> (level as u32)) & 1 == 0 {
                if node != V7_PAIR_EMPTY_ROOTS[level] {
                    (false, node)
                } else {
                    (true, node)
                }
            } else {
                (true, node)
            }
        }
        Err(_) => (false, [M31::ZERO; 8]),
    }
}

""" + DOC)
else:
    t = rsub(t, r'    let mut frontier = \[\[M31::ZERO; 8\]; POOL_V1_PAIR_TREE_DEPTH\];\n' + LOOP, """    let frontier = lane_frontier(tree, next_leaf_index)?;
""")
    t = sub(t, DOC, """/// One frontier node of the lane account image (level `level`): canonical, and equal to the pinned empty root where
/// the subtree is unoccupied (bit `level` of the next leaf index is 0); otherwise an error.
#[inline(always)]
fn lane_frontier_node(tree: &[u8], level: usize, next_leaf_index: u64) -> Result<[M31; 8], ProgramError> {
    use v7_pair_empty_roots::V7_PAIR_EMPTY_ROOTS;
    let start = 48 + 32 * level;
    let node = decode_digest_canonical(
        tree[start..start + 32]
            .try_into()
            .map_err(|_| ProgramError::InvalidAccountData)?,
    )
    .map_err(|_| ProgramError::InvalidAccountData)?;
    if (next_leaf_index >> (level as u32)) & 1 == 0 {
        if node != V7_PAIR_EMPTY_ROOTS[level] {
            Err(ProgramError::InvalidAccountData)
        } else {
            Ok(node)
        }
    } else {
        Ok(node)
    }
}

/// The frontier of the lane account image: its nodes, one per level, each as `lane_frontier_node` accepts it; an
/// error if any level is not acceptable.
#[inline(always)]
fn lane_frontier(tree: &[u8], next_leaf_index: u64) -> Result<[[M31; 8]; POOL_V1_PAIR_TREE_DEPTH], ProgramError> {
    let mut frontier = [[M31::ZERO; 8]; POOL_V1_PAIR_TREE_DEPTH];
    let mut frontier_ok = true;
    let mut level = 0;
    while level < POOL_V1_PAIR_TREE_DEPTH {
        match lane_frontier_node(tree, level, next_leaf_index) {
            Ok(node) => frontier[level] = node,
            Err(_) => frontier_ok = false,
        }
        level += 1;
    }
    if frontier_ok {
        Ok(frontier)
    } else {
        Err(ProgramError::InvalidAccountData)
    }
}

""" + DOC)
out[f] = t
# ------------------------------------------------------------------ candidate.rs: wide_view
# The struct it returns held `&[]`: at the MIR stage the tools read, that literal is a temporary of the function, so
# the returned value borrows a dead local ("There should be no bottoms in the value"). A named constant instead.
f = C + 'src/candidate.rs'; t = (T / f).read_text()
old = fn_text(t, "fn wide_view<'a>(")
new = sub(old, 'query_bytes: &[],', 'query_bytes: NO_QUERY_BYTES,')
t = sub(t, old, new)
t = sub(t, "/// View over the logical semantic/y1 buffers and the stored wide fields.\n", "/// The empty query-bytes slice of the views built here (a named constant, not a literal in the returned struct).\nconst NO_QUERY_BYTES: &[u8] = &[];\n/// View over the logical semantic/y1 buffers and the stored wide fields.\n")
out[f] = t
# ------------------------------------------------------------------ program adapter: lifecycle_accounts, close_checkpoint
# Both keep their pinned text. With the slice pattern over the accounts replaced by a length test and indexing (tried
# in the first batch, emission TP-A31p) the tools go past "Inconsistent projection" and stop elsewhere:
# `lifecycle_accounts` returns two references to account handles ("Unreachable" on the whole function), and
# `close_checkpoint` writes lamports and data through the SDK's `RefCell` handles ("Unreachable"). Neither is removed by
# a loop-form change, so no change is made; both are named gaps in the note.
for p, text in out.items():
    q = OUT / p; q.parent.mkdir(parents=True, exist_ok=True); q.write_text(text); print('wrote', p)
