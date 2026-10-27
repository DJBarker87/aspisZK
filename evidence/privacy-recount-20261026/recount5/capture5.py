from pathlib import Path
import subprocess,json,hashlib
P=Path(__file__).resolve().parent
refs={'research':'research','rw':'0c9dc9a4cc','cb':'codex/pv-cb-20261026','cb3':'codex/pv-cb3-20261026','cb9':'codex/pv-cb9-20261027','cbmid':'codex/pv-cbmid-20261027','op134':'codex/pv-op134-20261027','cblib':'codex/pv-cblib-20261027','route2':'codex/pv-route2-20261027','batch1':'codex/pv-batch1-20261027','runjoin':'codex/pv-runjoin-20261026','l2b':'codex/pv-l2b-20261027','l3':'codex/pv-l3-20261026','n7':'codex/pv-n7-20261027'}
# Historical consumer/extraction branches are immutable recount-4 pins when deleted.
old=json.loads((P.parent/'recount4/pins.json').read_text())
for k in ['join','extract']:refs[k]=old['revisions'][k]
def git(*a):return subprocess.check_output(['git',*a])
if not (P/'pins.json').exists():
 pins={k:git('rev-parse',v).decode().strip() for k,v in refs.items()}
 (P/'pins.json').write_text(json.dumps(dict(branches=refs,revisions=pins,worktree_base=git('rev-parse','HEAD').decode().strip()),indent=2)+'\n')
pins=json.loads((P/'pins.json').read_text())['revisions']; cache={};manifest=[]
oldobjects={p.name:p for p in (P.parent/'recount4/objects').glob('*.txt')}
def read(k,path):
 key=(k,path)
 if key in cache:return cache[key]
 q=subprocess.run(['git','show',pins[k]+':'+path],capture_output=True)
 if q.returncode:cache[key]=None;return None
 raw=q.stdout;blob=hashlib.sha1(b'blob '+str(len(raw)).encode()+b'\0'+raw).hexdigest()
 dest=oldobjects.get(blob+'.txt')
 if not dest:
  dest=P/'objects'/(blob+'.txt');dest.parent.mkdir(exist_ok=True);dest.write_bytes(raw)
 import os
 manifest.append(dict(ref=k,revision=pins[k],path=path,blob=blob,sha256=hashlib.sha256(raw).hexdigest(),snapshot=os.path.relpath(dest,P)))
 cache[key]=raw.decode();return cache[key]
rows=json.loads((P.parent/'recount4/rows4.json').read_text());audit=[]
for r in rows:
 path,_,decl=r.get('definition','').partition('#');sources=[]
 for k in pins:
  s=read(k,path)
  if s is not None:
   x=next(x for x in reversed(manifest) if x['ref']==k and x['path']==path)
   sources.append({**{v:x[v] for v in ['ref','path','blob','sha256']},'declaration':decl})
 audit.append(dict(id=r['id'],definition=r.get('definition',''),sources=sources,same_as_recount4=[x['ref'] for x in sources if x['sha256'] in {y['sha256'] for y in r['definition_witnesses']}]))
patterns=['docs/research/v8-r0-zk-20261009/lean/R1Z/*.lean','docs/research/v8-r0-zk-20261009/lean/PV_L2B*.lean','docs/research/100bit-spend-path-20261013/lean/prover-rw-20261023/*.lean','evidence/pv-*/*.md','design/PV-*.md']
for k,rev in pins.items():
 q=subprocess.run(['git','grep','-l','-e','.',rev,'--',*patterns],capture_output=True,text=True)
 for l in q.stdout.splitlines():read(k,l.split(':',1)[1])
 for path in ['docs/research/v8-r0-zk-20261009/LOG.md','design/PRIVACY-LEDGER-20261026.md','design/RELEASE-LEDGER-20261025.md','evidence/pv-join-20261026/wire/IMPORT-CHAIN.md']:
  read(k,path)
(P/'manifest.json').write_text(json.dumps(manifest,indent=2)+'\n');(P/'definition-audit5.json').write_text(json.dumps(audit,indent=2)+'\n')
print(len(pins),'pins',len(audit),'rows',len(manifest),'source records')
