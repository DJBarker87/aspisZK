#!/usr/bin/env python3
"""Aspis translatability pass, patch 0 (restoration): give every R1 function that the experiment edited its pinned text
back (c7593d23fdc), byte for byte, under #[cfg(not(<feature>))], and keep what the Aspis or experimental configuration
compiles as a SEPARATE definition of the same name under #[cfg(<feature>)]. No `if cfg!` inside an R1 function, no
pinned body in a renamed helper on the live path. Reads the pinned files with `git show`; reads the base tree from a
directory; writes the changed files to an output directory. Nothing else is touched.
usage: TP_restore.py <base dir> <out dir>      (run from the repository root)"""
import re, subprocess, sys, importlib.util
from pathlib import Path
BASE, OUT = Path(sys.argv[1]), Path(sys.argv[2]); PIN = 'c7593d23fdc'
# MODE 'p0' (default, third version of the patch): every changed R1 function EXCEPT `prepared_claim`. Restoring the
#   pinned `prepared_claim` costs 1,845 compute units on every measured case (it is inlined into `Prepared::new`, and
#   the compiler's register use in the claim loop differs once the experiment's `if cfg!` form is gone); with it left as
#   the base tree has it the restored build costs 3 units LESS than the base (bisect run b2: vP against the base).
#   `prepared_claim` is a rewrite candidate (CANNOT-EXTRACT CE03) and is dealt with by patch 1.
# MODE 'claim': only the `prepared_claim` split (used by the patch 1 builder as its first step).
# MODE 'v2': everything, as the superseded second version of the patch did.
MODE = sys.argv[3] if len(sys.argv) > 3 else 'p0'
assert MODE in ('p0', 'claim', 'v2')
spec = importlib.util.spec_from_file_location('fx', Path(__file__).with_name('TP_fntext.py'))
src_fx = Path(__file__).with_name('TP_fntext.py').read_text().split("rep = {}")[0].replace("A, B, OUT = sys.argv[1:4]; FILES = sys.argv[4:]", "")
fx = {}; exec(compile(src_fx, 'TP_fntext_head', 'exec'), fx)
def pin(f): return subprocess.check_output(['git', 'show', PIN + ':' + f]).decode()
def resolve(text, feature, on=True):
    """what the compiler keeps of `text` when `feature` is on: #[cfg(feature = "F")] / #[cfg(not(feature = "F"))] on an inner block or statement"""
    pat = re.compile(r'(?m)^[ \t]*#\[cfg\((not\()?feature\s*=\s*"%s"\)?\)\][ \t]*\n' % re.escape(feature))
    while True:
        m = pat.search(text)
        if not m: return text
        keep = (m.group(1) is None) == on
        if keep: text = text[:m.start()] + text[m.end():]; continue
        i = m.end(); depth = 0; j = i; seen_brace = False
        while j < len(text):
            ch = text[j]
            if ch in '([': depth += 1
            elif ch in ')]': depth -= 1
            elif ch == '{':
                if depth == 0:
                    d = 1; j += 1
                    while d:
                        if text[j] == '{': d += 1
                        elif text[j] == '}': d -= 1
                        j += 1
                    seen_brace = True; break
            elif ch == ';' and depth == 0:
                j += 1; break
            j += 1
        while j < len(text) and text[j] in ' \t': j += 1
        if j < len(text) and text[j] == '\n': j += 1
        text = text[:m.start()] + text[j:]
def sub(t, old, new):
    assert t.count(old) == 1, ('not unique', old[:80], t.count(old)); return t.replace(old, new)
NOTE = '/// Aspis new gate (replaces the pinned `%s` when `%s` is on); equality with the pinned function is owed.\n'
PLAN = {}   # file -> list of (key, feature cfg expr, builder(head_text) -> variant text, note name)
C = 'crates/aspis-r1-cost-probe/src/'; P = 'programs/r1-cost-probe/src/'
def feat(F): return 'feature = "%s"' % F
def on(F): return lambda h: resolve(h, F, True)
PLAN[C + 'r1_wire.rs'] = [
 ('::validate_record_fields#1', feat('future-lean-parse'), lambda h: 'fn validate_record_fields(row: u8, payload: &[u8]) -> Result<(), Error> {\n    validate_record_fields_lean(row, payload)\n}', 'validate_record_fields'),
 ("impl <'a> ValidatedRecord<'a>::decode_k#1", feat('future-validated-decode'), on('future-validated-decode'), 'decode_k'),
]
PLAN[C + 'candidate.rs'] = [
 ('::canonical_scan#1', feat('future-word-scan'), lambda h: '#[inline(never)]\nfn canonical_scan(proof: &[u8]) -> Result<(), Error> {\n    canonical_scan_words(proof)\n}', 'canonical_scan'),
 ('::batch_tree#1', feat('future-merkle-single-pass'), on('future-merkle-single-pass'), 'batch_tree'),
]
PLAN[C + 'fast_pairing.rs'] = [
 ('impl EbyKDot::push#1', feat('future-lean-dot'), lambda h: '    #[inline(always)]\n    pub fn push(&mut self, value: E, scalar: QM31) -> Result<(), ()> {\n        self.push_lean(value, scalar);\n        Ok(())\n    }', 'EbyKDot::push'),
]
def claim_rows(h):
    a = h.index('        if cfg!(feature="future-claim-rows") {\n'); b = h.index('        } else {\n'); c = h.index('        let mut claim=E::ZERO;')
    inner = h[a + len('        if cfg!(feature="future-claim-rows") {\n'):b]
    inner = '\n'.join(l[4:] if l.startswith('            ') else l for l in inner.split('\n'))
    return h[:a] + inner + h[c:]
PLAN[C + 'verifier.rs'] = [('::prepared_claim#1', 'feature="future-claim-rows"', claim_rows, 'prepared_claim')]
PLAN[C + 'r1_semantic.rs'] = [
 ('::semantic_boundary#1', feat('future-lazy-boundary'), on('future-lazy-boundary'), 'semantic_boundary'),
 ('::semantic_value#1', feat('future-lazy-horner'), lambda h: h, 'semantic_value'),
]
PLAN[P + 'r1_pool_adapter.rs'] = [('::scan_proof_buffer#1', feat('future-one-tx'), on('future-one-tx'), 'scan_proof_buffer')]
PLAN[P + 'r1_pool_adapter_owned.rs'] = [
 ('::stage2_owned#1', feat('future-one-tx'), on('future-one-tx'), 'stage2_owned'),
 ('::stage1#1', feat('future-one-tx-lean'), on('future-one-tx-lean'), 'stage1'),
 ('::stage2#1', feat('future-one-tx'), on('future-one-tx'), 'stage2'),
]
if MODE == 'p0': del PLAN[C + 'verifier.rs']
if MODE == 'claim': PLAN = {C + 'verifier.rs': PLAN[C + 'verifier.rs']}
report = []
for f, items in PLAN.items():
    t = (BASE / f).read_text(); pf = fx['fns'](pin(f))
    for key, cfg, build, name in items:
        hf = fx['fns'](t); head = hf[key]['text']; pinned = pf[key]['text']
        assert t.count(head) == 1, (f, key)
        ind = re.match(r'[ \t]*', head).group(0)
        variant = build(head)
        assert variant != pinned, (f, key, 'variant equals pinned text')
        new = '%s#[cfg(not(%s))]\n%s\n%s%s%s#[cfg(%s)]\n%s' % (ind, cfg, pinned, ind, NOTE % (name, cfg.split('"')[1]), ind, cfg, variant)
        t = t.replace(head, new); report.append((f, key, cfg))
    (OUT / f).parent.mkdir(parents=True, exist_ok=True); (OUT / f).write_text(t)
if MODE == 'claim':
    for r in report: print(*r)
    sys.exit(0)
# the program entry: the pinned text when the adapter is built (R1 and Aspis alike); the measurement entry otherwise
f = P + 'lib.rs'; t = (BASE / f).read_text(); key = '::process_r1_cost_probe_instruction#1'
head = fx['fns'](t)[key]['text']; pinned = fx['fns'](pin(f))[key]['text']; assert t.count(head) == 1
t = t.replace(head, '#[cfg(feature = "pool-adapter")]\n' + pinned + '\n/// Measurement entry of the experiment (no Pool adapter); never part of a deployed program.\n#[cfg(not(feature = "pool-adapter"))]\n' + head)
(OUT / f).parent.mkdir(parents=True, exist_ok=True); (OUT / f).write_text(t); report.append((f, key, 'feature = "pool-adapter" (pinned) / not (measurement entry)'))
# the two renamed helpers that hold a pinned body stay as test oracles only
f = C + 'r1_wire.rs'; t = (OUT / f).read_text()
t = sub(t, 'fn validate_record_fields_pinned(row: u8, payload: &[u8]) -> Result<(), Error> {', '/// Test oracle only: a copy of the pinned body of `validate_record_fields`.\n#[cfg(test)]\nfn validate_record_fields_pinned(row: u8, payload: &[u8]) -> Result<(), Error> {')
(OUT / f).write_text(t)
f = C + 'candidate.rs'; t = (OUT / f).read_text()
t = sub(t, '#[inline(never)]\nfn canonical_scan_pinned(proof: &[u8]) -> Result<(), Error> {', '/// Test oracle only: a copy of the pinned body of `canonical_scan`.\n#[cfg(test)]\n#[inline(never)]\nfn canonical_scan_pinned(proof: &[u8]) -> Result<(), Error> {')
(OUT / f).write_text(t)
# `semantic_value` is switched on the lazy Horner step, which is a feature of aspis-core. A crate cannot test another
# crate's feature, so the verifier crate gets a feature of the same name that turns the aspis-core one on, and the
# program's feature turns both on. Without this the deployed build would compile the pinned `semantic_value`
# (multiply, then add) and lose the single-reduction step: the first version of this patch did exactly that.
f = 'crates/aspis-r1-cost-probe/Cargo.toml'; t = (BASE / f).read_text()
t = sub(t, 'future-lean-dot = []\n', 'future-lean-dot = []\n# G2 seen from this crate: selects the Aspis `semantic_value` and turns on the single-reduction\n# multiply-add of aspis-core. Builds of this crate must name THIS feature, not `aspis-core/future-lazy-horner`.\nfuture-lazy-horner = ["aspis-core/future-lazy-horner"]\n')
(OUT / f).write_text(t); report.append((f, 'feature future-lazy-horner added', ''))
f = 'programs/r1-cost-probe/Cargo.toml'; t = (BASE / f).read_text()
t = sub(t, 'future-lazy-horner = ["aspis-core/future-lazy-horner"]\n', 'future-lazy-horner = ["aspis-core/future-lazy-horner", "aspis-r1-cost-probe/future-lazy-horner"]\n')
(OUT / f).write_text(t); report.append((f, 'feature future-lazy-horner forwards to the verifier crate', ''))
for r in report: print(*r)
