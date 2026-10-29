"""Keep the accepted translator; remove only this resume's compiled scratch."""
from pathlib import Path
import hashlib,json,shutil,subprocess
H=Path('/home/dombarker/project-offloads/codex-pv-cx-20261029/resume-ae1')
receipts=[p for p in H.glob('N*/receipt.json')]
statuses={}
for p in receipts:
 n=p.parent.name[1:]
 if n=='73330':continue
 r=subprocess.run(['systemctl','--user','is-active',f'PV_CX2_N{n}.scope'],capture_output=True,text=True)
 statuses[n]=dict(exit=r.returncode,status=r.stdout.strip());assert r.returncode!=0,('scope active',n)
src=H/'aeneas/src/_build/default/main.exe';O=H/'pinned-tools';O.mkdir()
dst=O/'aeneas-ae1-2-fda587d2';shutil.copy2(src,dst)
sha=hashlib.sha256(dst.read_bytes()).hexdigest();assert sha=='fda587d25a66604a973bbc2947a4416ba373b56dd8c98655991c1b6eaa240b68'
paths=[H/'charon-target',H/'charon/_build',H/'aeneas/src/_build',H/'deps']
for p in paths:
 assert p.is_relative_to(H) and p not in [H,H.parent]
 subprocess.run(['sudo','-n','rm','-rf','--',str(p)],check=True)
record=dict(retained_binary=dict(path=str(dst),sha256=sha,bytes=dst.stat().st_size),removed_compiled_scratch=[str(p) for p in paths],scopes=statuses,key_operations='none: no wallet/account keys generated or touched; no source/raw LLBC/evidence removed',installed_translators_unchanged=True)
(H/'cleanup.json').write_text(json.dumps(record,indent=2)+'\n');print(json.dumps(record))
