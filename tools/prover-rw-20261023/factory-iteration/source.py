"""Check source identity and exact erasure of the only factory annotation."""
from pathlib import Path
import hashlib,json,subprocess,sys
D=Path(__file__).resolve().parent
C=D.parent/'factory-cleanup'
subprocess.run([sys.executable,str(C/'source.py'),'--check'],check=True)
annotation='        #[cfg_attr(kani, kani::loop_invariant(unsafe { retry <= limit && retry == checks::CALLS && checks::PRIOR_REJECTED && checks::LAST_ERROR.is_none() && (retry == 0 || checks::PROVIDER_STATE == checks::LAST_STATE) }))]\n'
selected=(D/'proof/selected.rs').read_text()
assert selected.count(annotation)==1
assert selected.replace(annotation,'')==(C/'proof/selected.rs').read_text()
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
out=dict(schema='ProverRwFactoryIteration-source-erasure-v1',production_map=json.loads((C/'source-map.json').read_text()),production_map_sha256=sha(C/'source-map.json'),selected_sha256=sha(D/'proof/selected.rs'),annotation=annotation,annotation_count=1,erased_selected_sha256=sha(C/'proof/selected.rs'),association='Only retry-loop proof annotation added; deleting it recovers exact immutable source-selected items. No executable production span altered.',scope='Byte erasure is checked; correctness of Kani invariant instrumentation is the pinned tool boundary, not a proved event-erasure contract.')
p=D/'source-map.json'
if '--check' in sys.argv:assert json.loads(p.read_text())==out
else:p.write_text(json.dumps(out,indent=2)+'\n')
print('factory iteration annotation erasure checked')
