from pathlib import Path
import subprocess,json,shlex,hashlib,sys
D='/home/dombarker/project-offloads/codex-pv-op223-20261027';H='dombarker@100.108.41.90';E=Path('evidence/pv-op223-20261027')
# Same source/tool; final native feature matrix is the recorded changed environment.
base=json.loads((E/'charon-applied-001/target.json').read_text())['target'];base[base.index('--features')+1]='optimized-terminal,r1p-check,ct-host-prover';base[base.index('--dest-file')+1]=D+'/PV_Op223_AppliedFinal.llbc'
for label,cmd in ([] if '--collect-only' in sys.argv else [('charon-applied-final-002',base),('aeneas-applied-final-002',['timeout','120','/home/dombarker/project-offloads/codex-pv-cb-20261026/pinned-tools/aeneas','-sequential','-no-progress-bar','-abort-on-error','-strict-joins','-backend','lean','-namespace','PV_Op223_Applied','-dest',D+'/applied-final-generated','-split-files','-emit-json',D+'/PV_Op223_AppliedFinal.llbc'])]):
 r=subprocess.run(['ssh',H,shlex.join(['python3',D+'/run_host.py',label,json.dumps(cmd)])]);
 if r.returncode:sys.exit(r.returncode)
rows={}
for name in ['Funs.lean','Types.lean']:
 raw=subprocess.check_output(['ssh',H,'cat '+D+'/applied-final-generated/'+name]);old=(E/('raw-'+name)).read_bytes();normalized=raw.replace(b'import PVOp223AppliedFinal.Types',b'import PVOp223Applied.Types');rows[name]=dict(final_sha256=hashlib.sha256(raw).hexdigest(),initial_sha256=hashlib.sha256(old).hexdigest(),byte_identical=raw==old,declaration_bytes_identical=normalized==old,adaptation='Generated Types import stem follows the changed llbc basename; no declaration change');assert normalized==old
(E/'final-feature-extraction-identity.json').write_text(json.dumps(rows,indent=2)+'\n')
