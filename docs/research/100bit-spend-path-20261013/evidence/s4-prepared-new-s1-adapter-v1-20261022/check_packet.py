from pathlib import Path
import hashlib,json,sys
p=Path(__file__).resolve().parent
sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest()
receipt=json.loads((p/'proof/receipt.json').read_text())
src=p/'sources/S4PreparedNewS1AdapterV1.lean'
assert receipt['exit_status']==0
assert receipt['source_sha256']==sha(src)
assert receipt['object_sha256']=='329c4235c40437f1b3408ebf4187ceb2104425c077594ed9ca54bb245621678c'
assert receipt['axioms']=='[propext, Classical.choice, Quot.sound]'
assert '#print axioms AspisR1S4PreparedNewS1AdapterV1.prepareByS1Body_success_powers' in src.read_text()
source_pin=json.loads((p/'dependency-pins/prepared-new-source.json').read_text())
current=(p/'dependency-pins/current-prepared-new-fragment.rs').read_text()
s1=(p/'dependency-pins/s1-prepared-new-fragment.rs').read_text()
assert sha((p/'dependency-pins/current-prepared-new-fragment.rs'))==source_pin['current_fragment_sha256']
assert sha((p/'dependency-pins/s1-prepared-new-fragment.rs'))==source_pin['s1_fragment_sha256']
assert s1.removeprefix('    #[inline(never)]\n').rstrip()==current.rstrip()
log=(p/'proof/axioms-and-lean.log').read_text()
assert 'depends on axioms: [propext,' in log and 'Classical.choice' in log and 'Quot.sound' in log
assert 'sorryAx' not in log and 'sorryAx' not in src.read_text()
for f in p.rglob('*'):
 if f.is_file() and f.suffix in {'.olean','.ilean','.llbc','.a','.so','.dylib'}:
  raise AssertionError(f'compiled/binary artifact included: {f}')
for line in (p/'SHA256SUMS').read_text().splitlines():
 h,rel=line.split('  ',1); assert sha(p/rel)==h,rel
for pin in ['CurrentPreparedScratchReachability.json','CurrentPreparedScratchModel.json','CurrentCallerTypes.json']:
 d=json.loads((p/'dependency-pins'/pin).read_text())
 assert sha(Path(d['selected_object']))==d['sha256'],d['module']
print('PASS: source/object/axiom/receipt/import pins and source-only packet checks')
