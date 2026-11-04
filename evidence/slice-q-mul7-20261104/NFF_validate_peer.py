"""Revalidate immutable sibling snapshot in a private input mirror."""
from pathlib import Path
import subprocess,json,lzma,base64,hashlib,tempfile,os
E=Path(__file__).resolve().parent;R=E.parent.parent
x=json.loads(lzma.decompress((E/'NFF_NFB_IMPORT.json.xz').read_bytes()))
with tempfile.TemporaryDirectory(prefix='NFF_peer_validator_') as d:
 root=Path(d);(root/'evidence').mkdir()
 for p in R.iterdir():
  if p.name!='evidence':(root/p.name).symlink_to(p,target_is_directory=p.is_dir())
 for p in E.parent.iterdir():
  if p.name!='slice-q-compose5-20261104':(root/'evidence'/p.name).symlink_to(p,target_is_directory=p.is_dir())
 for f in x['files']:
  data=base64.b64decode(x['blobs'][f['git_blob']]['base64']);assert hashlib.sha256(data).hexdigest()==x['blobs'][f['git_blob']]['sha256']
  p=root/f['path'];p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(data)
 script=root/'evidence/slice-q-compose5-20261104/NFB_validate.py'
 env={**os.environ,'PYTHONDONTWRITEBYTECODE':'1'}
 r=subprocess.run(['python3',str(script)],cwd=root,env=env,capture_output=True,text=True)
 (E/'NFF_NFB_VALIDATOR.log').write_text(r.stdout+r.stderr)
 out=dict(revision=x['revision'],exit_status=r.returncode,command=['python3','NFB_validate.py'],script_sha256=hashlib.sha256(script.read_bytes()).hexdigest(),output_sha256=hashlib.sha256((r.stdout+r.stderr).encode()).hexdigest(),inputs='committed sibling archive plus read-only current baseline evidence',mutated_validators=False)
 if r.returncode==0:out['delta']=json.loads(r.stdout.splitlines()[-1])
 (E/'NFF_NFB_VALIDATION.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out))
