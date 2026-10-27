"""Read-only covered-source identity audit, no compilation or source mutation."""
from pathlib import Path
import subprocess,json,hashlib
root=Path(__file__).resolve().parents[2]
files=['crates/aspis-core/src/'+x for x in ['field.rs','field/ct.rs','field/wide_exact.rs','state_only_hiding.rs','state_only_prefix.rs','circle.rs','transcript.rs']]+['crates/aspis-r1-cost-probe/src/'+x for x in ['sampler.rs','ct_pole.rs','host_semantic.rs']]+['crates/aspis-statement/src/'+x for x in ['logup.rs','pool_v1/pair_trace.rs','pool_v1/pair_forest_trace.rs']]
code='''from pathlib import Path
import json,hashlib
b=Path('/home/dombarker/project-offloads/codex-pv-cb-20261026/source')
r={}
for f in FILES:
 p=b/f;r[f]={'sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'bytes':p.stat().st_size,'resolved':str(p.resolve())}
print(json.dumps(r))
'''.replace('FILES',repr(files))
remote=json.loads(subprocess.check_output(['ssh','dombarker@100.108.41.90','python3','-'],input=code,text=True))
refs=['HEAD','codex/cx-prover-rw-20261023'];pins={r:subprocess.check_output(['git','rev-parse',r],cwd=root,text=True).strip() for r in refs}
for f in files:
 for ref in refs:
  s=subprocess.check_output(['git','show',ref+':'+f],cwd=root)
  remote[f][ref+'_sha256']=hashlib.sha256(s).hexdigest();remote[f]['matches_'+ref]=remote[f]['sha256']==remote[f][ref+'_sha256']
capture=root/'tools/pv-cb-20261026/step-proof/captured_mask.rs'
actual=(root/'crates/aspis-core/src/state_only_hiding.rs').read_text()
text=capture.read_text()
normalized='\n'.join(('//'+line[3:]) if line.startswith('//!') else line for line in actual.split('\n'))
r=dict(branch_refs=pins,source_identity=remote,captured_mask=dict(sha256=hashlib.sha256(text.encode()).hexdigest(),verbatim_current_branch_prefix=text.startswith(actual),documentation_comment_normalized_prefix=text.startswith(normalized),documentation_change='Only inner //! documentation comments become ordinary // comments before proof-only exports',note='Extra cfg(kani)-only step projections follow the retained source. This syntactic audit does not prove source-erasure, native equivalence or effects.'),scope='Covered source hashes only, not an ELF or compiler reproducibility certificate')
(root/'evidence/pv-cb-20261026/RESUME4-NATIVE-SOURCE-IDENTITY.json').write_text(json.dumps(r,indent=2)+'\n')
print('covered files',len(files),'own branch matches',sum(v['matches_HEAD'] for v in remote.values()),'current read-only candidate matches',sum(v['matches_codex/cx-prover-rw-20261023'] for v in remote.values()),'capture prefix',r['captured_mask']['verbatim_current_branch_prefix'])
