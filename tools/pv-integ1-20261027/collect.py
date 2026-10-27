from pathlib import Path
import subprocess,json,sys
E=Path('evidence/pv-integ1-20261027');D='/home/dombarker/project-offloads/codex-pv-integ1-20261027';H='dombarker@100.108.41.90'
for label in (sys.argv[1:] or ['charon-applied-001','aeneas-applied-001','lean-43300']):
 out=E/label;out.mkdir(exist_ok=True)
 code="from pathlib import Path; import json; p=Path("+repr(D+'/'+label)+"); print(json.dumps([str(f.relative_to(p)) for f in p.rglob('*') if f.is_file()]))"
 files=json.loads(subprocess.check_output(['ssh',H,'python3 -c '+__import__('shlex').quote(code)],text=True))
 for f in files:
  if f.endswith(('.json','.log')) and (f.startswith('receipt/') or '/' not in f) and 'keypair' not in f:
   target=out/f;target.parent.mkdir(exist_ok=True,parents=True);subprocess.run(['scp','-q',H+':'+D+'/'+label+'/'+f,str(target)],check=True)
