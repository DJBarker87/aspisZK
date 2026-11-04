from pathlib import Path
import subprocess,json,hashlib
E=Path(__file__).resolve().parent
H='/home/dombarker/project-offloads/'
configs={}
for credit,orig,root in [('C044','K79200','codex-pv-k3scan-20261101/pathbuf'),('C088','K79220','codex-pv-k3scan-20261101/split-source'),('C089','K79222','codex-pv-k3scan-20261101/split-source')]:
 configs[credit]={'root':H+root,'pins':json.loads((E/f'original/{orig}/source-sha256.json').read_text())}
d=json.loads((E/'original/K12/source-manifest.json').read_text());configs['C084']={'root':H+'codex-pv-kstub-20261028','pins':{x['path']:x['sha256'] for x in d if x['path'].startswith('cblib/') or x['path']=='KMX_stubs.rs'}}
for c in ['K93109','K93110','K93111']:configs[c]={'root':H+'codex-pv-stx-20261104/native-source','pins':json.loads((E/'original/stx-source-sha256.json').read_text())}
tools=json.loads((E/'original/tools.json').read_text())['tools']
code='''from pathlib import Path
import json,hashlib,subprocess,time
configs=CONFIGS
tools=TOOLS
out={'epoch':time.time(),'credits':{},'tools':{}}
def sha(p):return hashlib.file_digest(p.open('rb'),'sha256').hexdigest()
for c,d in configs.items():
 rows=[]
 for rel,want in d['pins'].items():
  p=Path(d['root'])/rel;got=sha(p) if p.is_file() else None
  rows.append({'path':str(p),'expected':want,'actual':got,'match':got==want})
 out['credits'][c]={'root':d['root'],'rows':rows,'exact':all(x['match'] for x in rows)}
for n,d in tools.items():
 p=Path(d['path']);got=sha(p) if p.exists() else None
 out['tools'][n]={'path':str(p),'expected':d['sha256'],'actual':got,'match':got==d['sha256']}
q=Path('/home/dombarker/project-offloads/QUIET_WINDOW.json');out['quiet_marker']=q.read_text() if q.exists() else None
print(json.dumps(out))
'''.replace('CONFIGS',repr(configs)).replace('TOOLS',repr(tools))
r=subprocess.run(['ssh','dombarker@100.108.41.90','python3','-'],input=code,text=True,capture_output=True);assert r.returncode==0,r.stderr
out=json.loads(r.stdout);(E/'preflight.json').write_text(json.dumps(out,indent=2)+'\n')
print('tools:',{k:v['match'] for k,v in out['tools'].items()})
for c,d in out['credits'].items():print(c,d['exact'],[x for x in d['rows'] if not x['match']][:12])
(E/'source-config.json').write_text(json.dumps(configs,indent=2)+'\n')
