"""Check the private instrumentation's branch spine against source-bound control."""
from pathlib import Path
import hashlib,json,re,sys
E=Path('evidence/pv-evh10-20261102')
a=Path('lean/PV_EVH_LinuxRawControl.lean').read_text()
b=Path('lean/PV_EVH_LinuxRawHistory.lean').read_text()
control=a[a.index('match r.result with'):a.index('/-- The opaque')].strip()
private=b[b.index('let tail := match r.result with')+len('let tail := '):b.index('{tail with calls := current :: tail.calls}')].strip()
normalize=lambda x:re.sub(r'\s+','',x)
assert normalize(control)==normalize(private),'private instrumentation changed source control'
assert 'theorem erases' in b and '#print axioms erases' in b
assert 'theorem first_call' in b and '#print axioms first_call' in b
assert 'NativeEvent' not in b.replace('NOT a NativeEvent','')
sha=lambda s:hashlib.sha256(s.encode()).hexdigest()
out=dict(evidence_class='private source-control instrumentation with Lean erasure law',
 control_sha256=sha(a),instrumentation_sha256=sha(b),branch_spine_sha256=sha(normalize(control)),
 source_binding='getrandom-linux-raw-binding.json',laws=['PV_EVH_LinuxRawHistory.erases','PV_EVH_LinuxRawHistory.first_call'],
 retains='Ordered private call receipts contain address, remaining length, complete before/after buffers, status, OS world before/after and kernel observation prefix. Nothing publishes this private receipt as a NativeEvent.',
 limits=['actual syscall memory footprint remains P','original machine-frame address and spatial separation remain P','private trace not yet carried through complete native entry or connected to L3 joint observer','no successful actual run or full trace projection claimed'],
 trust_fields_added=[],rows_removed=[])
p=E/'getrandom-private-history-binding.json'
if '--check' in sys.argv:assert json.load(open(p))==out
else:p.write_text(json.dumps(out,indent=2)+'\n')
print('PASS private raw-syscall history branch spine; full native/L3 association remains OPEN')
