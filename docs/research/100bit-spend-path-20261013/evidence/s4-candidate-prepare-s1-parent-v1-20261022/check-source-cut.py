#!/usr/bin/env python3
import hashlib, json, re, sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[4]
manifest = json.loads((HERE / 'manifest.json').read_text())
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def require(ok, msg):
    if not ok: raise SystemExit('FAIL: ' + msg)

source = HERE / 'sources/S4CandidatePrepareS1ParentV1.lean'
require(sha(source) == manifest['source_sha256'], 'Lean source hash')
for name, info in manifest['pins'].items():
    p = HERE / 'source-pins' / name
    require(p.is_file() and sha(p) == info['sha256'], f'pin hash {name}')
for name, info in manifest['rust_sources'].items():
    p = ROOT / info['path']
    require(p.is_file() and sha(p) == info['sha256'], f'frozen Rust source {name}')

# Compare the complete copied prepare body against the exact emitted body,
# permitting only the explicit leaf-slot substitutions and Prepared.new cut.
orig = (HERE / 'source-pins/AspisR1CurrentCaller-Funs.lean').read_text()
orig = orig[orig.index('  := do\n', orig.index('def verifier.candidate.prepare')) + len('  := do\n'):]
orig = orig[:orig.index('\n/-- [aspis_r1_cost_probe::compact::OFF_FOLDED_ROOT]')]
ours = source.read_text()
ours = ours[ours.index(' := do\n', ours.index('def prepareWithS1New')) + len(' := do\n'):]
ours = ours[:ours.index('\ndef prepareSlot')]
patterns = [
(r'core\.result\.Result\.map_err\s*\(verifier\.candidate\.prepare\.closure\.Insts\.CoreOpsFunctionFnOnceTupleErrorError\s*aspis_coredigestDigest32Inst\)\s*r\s*\(\)', 'ops.mapAllocError r'),
(r'core\.result\.Result\.map_err\s*\(verifier\.candidate\.prepare\.closure_1\.Insts\.CoreOpsFunctionFnOnceTupleErrorError\s*aspis_coredigestDigest32Inst\)\s*r5\s*\(\)', 'ops.mapWireError r5'),
(r'aspis_core\.r0\.heap\.filled core\.marker\.CopyU8', 'ops.filled'),
(r'compact\.LOGICAL_SEMANTIC','ops.logicalSemantic'), (r'compact\.LOGICAL_Y1','ops.logicalY1'),
(r'compact\.OFF_SEMANTIC','ops.offSemantic'), (r'compact\.OFF_Y1','ops.offY1'), (r'compact\.OFF_INACTIVE','ops.offInactive'),
(r'compact\.expand_semantic','ops.expandSemantic'), (r'compact\.expand_values','ops.expandValues'),
(r'verifier\.candidate\.wide_view','ops.wideView'),
(r'r1_semantic\.verify_observed\s+aspis_coredigestDigest32Inst','ops.verifyObserved d'),
(r'verifier\.mark','ops.mark'),
(r'verifier\.Prepared\.new\s+aspis_coredigestDigest32Inst','prepareByS1Body B d'),
(r'verifier\.Error\.Insts\.CoreConvertFromCodecError','ops.codecFrom'),
(r'verifier\.Prepared','Prepared'), (r'verifier\.Error','VError'),
(r'let i ← ops\.mark obs AspisR1CurrentCaller\.VError\.Phase\.Semantic','ops.mark obs verifier.Phase.Semantic'),
(r'AspisR1CurrentCaller\.verifier\.Prepared','Prepared'), (r'AspisR1CurrentCaller\.verifier\.Error','VError'),
(r' U8\)', ' Std.U8)'),
]
for pattern, replacement in patterns: orig = re.sub(pattern, replacement, orig)
orig = re.sub(r'SliceIndexRangeUsizeSlice\s+Std\.U8','SliceIndexRangeUsizeSlice U8',orig)
orig = re.sub(r'SliceIndexRangeToUsizeSlice\s+Std\.U8','SliceIndexRangeToUsizeSlice U8',orig)
orig = re.sub(r'SliceIndexRangeFromUsizeSlice\s+Std\.U8','SliceIndexRangeFromUsizeSlice U8',orig)
orig = orig.replace('AspisR1CurrentCaller.verifier.Phase.Semantic','verifier.Phase.Semantic')
orig = orig.replace('verifier.Prepared','Prepared').replace('verifier.Error','VError')
orig = orig.replace('AspisR1CurrentCaller.verifier.Prepared','Prepared').replace('AspisR1CurrentCaller.verifier.Error','VError')
orig = re.sub(r'(?m)^\s*ops\.mark obs AspisR1CurrentCaller\.verifier\.Phase\.Semantic\s*$', 'ops.mark obs verifier.Phase.Semantic', orig)
orig = orig.replace('ops.mark obs verifier.Phase.Semantic\n            prepareByS1Body', 'let _ ← ops.mark obs verifier.Phase.Semantic\n            prepareByS1Body')
ours = ours.replace('AspisR1CurrentCaller.verifier.Prepared','Prepared').replace('AspisR1CurrentCaller.verifier.Error','VError').replace('AspisR1CurrentCaller.verifier.Phase','verifier.Phase')
tok = lambda x: re.findall(r'\w+|[^\s\w]', x)
require(tok(orig) == tok(ours), 'normalized generated-body token comparison')

text = source.read_text()
require('sorry' not in text and not re.search(r'(?m)^\s*axiom\s', text), 'forbidden proof escape')
for p in HERE.rglob('*'):
    if p.is_file():
        require(p.suffix not in {'.olean','.llbc','.bin'}, f'compiled/binary artifact included: {p}')
receipt = json.loads((HERE/'proof/receipt.json').read_text())
require(receipt['exit_status'] == 0 and receipt['source_sha256'] == manifest['source_sha256'], 'compile receipt')
require(receipt['object_sha256'] == manifest['object_sha256'], 'compiled object hash')
log=(HERE/'proof/lean.log').read_text()
for theorem in manifest['theorems']:
    matches=re.findall(r"'AspisR1S4CandidatePrepareS1ParentV1\.%s' depends on axioms: \[(.*?)\]" % re.escape(theorem), log, re.S)
    require(len(matches)==1, f'axiom report for {theorem}')
    names=set(re.findall(r'[A-Za-z][A-Za-z0-9_.]*',matches[0]))
    require(names == set(manifest['accepted_axioms']), f'axioms for {theorem}: {sorted(names)}')
print('PASS: frozen source pins, generated-body token cut, receipts, axioms, and source-only artifact policy')
