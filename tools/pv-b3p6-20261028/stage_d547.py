"""Stage only job-owned new sources with their committed h5 authority."""
from pathlib import Path
import subprocess,json,hashlib,re
H='/home/dombarker/project-offloads/codex-pv-b3p6-20261028';D=Path('evidence/pv-b3p6-20261028')
revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip();sources={};authority={}
for name in ['PV_B3P_DigestSource547227','PV_B3P_PathSource547227','PV_B3P_PackedExternal547227']:
 p=D/'lean'/(name+'.lean');raw=subprocess.check_output(['git','show',revision+':'+str(p)]);assert raw==p.read_bytes()
 sources[name]=raw.decode();authority[name]=dict(module=name,path=str(p),blob=subprocess.check_output(['git','rev-parse',revision+':'+str(p)],text=True).strip(),sha256=hashlib.sha256(raw).hexdigest(),authority='h5 HEAD',imports=re.findall(r'^import (\S+)',raw.decode(),re.M),tracked_conflicts=[])
scripts={n:Path('tools/pv-b3p6-20261028/'+n).read_text()for n in ['queue_lean547_host.py','collect_d547_host.py','reference_packed547_host.py']}
code='''from pathlib import Path
import json,hashlib
H=Path(HOST); sources=SOURCES;authority=AUTHORITY;scripts=SCRIPTS
for n,s in sources.items():
 p=H/'lean'/(n+'.lean');assert not p.exists() or p.read_text()==s;p.write_text(s)
p=H/'project-resolution-resume18.json';x=json.loads(p.read_text());x['revision']=REVISION;x['modules'].update(authority);p.write_text(json.dumps(x,indent=2)+'\\n')
for n,s in scripts.items():(H/n).write_text(s)
print(json.dumps(dict(staged=list(sources),authority_revision=REVISION)))
'''.replace('HOST',repr(H)).replace('SOURCES',repr(sources)).replace('AUTHORITY',repr(authority)).replace('SCRIPTS',repr(scripts)).replace('REVISION',repr(revision))
print(subprocess.check_output(['ssh','dombarker@100.108.41.90','python3','-'],input=code,text=True),end='')
