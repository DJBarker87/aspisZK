#!/usr/bin/env python3
"""Recover the exact source of given closure modules (method of L187_SOURCE_MANIFEST.json):
object identity = a surviving host copy byte-identical to the overlay object at a successful
committed receipt's -o path; source = committed blob whose sha256 equals that receipt's recorded
source hash. Usage: L187_recover.py out.json Module1 Module2 ..."""
import json,subprocess,sys,re,collections,hashlib,os
REPO='/Users/dominic/ZK/.worktrees/cx-integrate'; os.chdir(REPO)
H='dombarker@100.108.41.90'
S='/private/tmp/claude-501/-Users-dominic-ZK/3db59790-41f3-4c53-ae90-3fc42a8cab96/scratchpad/'
outp,mods=sys.argv[1],sys.argv[2:]
plan=json.load(open(S+'l187_plan.json'))['plan']
pats=[m.replace('.','/')+'.lean"' for m in mods]
r=subprocess.run(['git','grep','-l','-F',*sum([['-e',p] for p in pats],[]),'HEAD','--','*.json'],capture_output=True,text=True)
files=[l.split(':',1)[1] for l in r.stdout.splitlines()]
mp2m={m.replace('.','/')+'.olean':m for m in mods}
cands=collections.defaultdict(list)
for f in files:
  t=subprocess.run(['git','show','HEAD:'+f],capture_output=True,text=True).stdout
  recs=[]
  try: recs=[json.loads(t)]
  except Exception: recs=[json.loads(l) for l in t.splitlines() if l.strip().startswith('{')]
  for x in recs:
    if not isinstance(x,dict): continue
    cmd=x.get('command') or []
    if '-o' not in cmd: continue
    o=cmd[cmd.index('-o')+1]; m=next((mp2m[k] for k in mp2m if o==k or o.endswith('/'+k)),None)
    if m and f.endswith('receipt.json') and x.get('exit_status')==0:
      cands[m].append(dict(file=f,attempt=x.get('attempt'),out=o,sources=x.get('sources'),source_hashes=x.get('source_hashes')))
q=json.dumps(dict(rels=sorted({m.replace('.','/')+'.olean' for m in mods}),overlays=[plan[m]['overlay'] for m in mods]))
h=json.loads(subprocess.run(['ssh',H,'python3 /home/dombarker/project-offloads/codex-cx-replay-l187-20261109/L187_hostcopies.py'],input=q,capture_output=True,text=True,timeout=3000).stdout)
copies=collections.defaultdict(list)
for x,p in h['copies']: copies[x].append(p)
idx=json.load(open(S+'lean_sha_index.json'))  # sha256 -> committed .lean/.lean.txt paths at HEAD
def anum(a):
  m=re.search(r'(\d+)[a-z]?$',a or ''); return int(m.group(1)) if m else -1
out={}
for m in mods:
  ch=h['overlay'][plan[m]['overlay']]; same=copies[ch]
  hits=sorted([x for x in cands[m] if any(p.endswith('/'+x['out']) for p in same)],key=lambda x:anum(x['attempt']),reverse=True)
  res=None
  for x in hits:
    src=(x['sources'] or [None])[0]; rh=(x['source_hashes'] or {}).get(src)
    if not rh: continue
    if rh in idx:
      ps=sorted(idx[rh],key=lambda p:('/sources/' in p,len(p)))
      res=dict(status='RECOVERED_BY_HASH',producing_attempt=x['attempt'],receipt=x['file'],path=ps[0],sha256=rh,other_paths=ps[1:6])
    if res: break
  out[m]=res or dict(status='UNRECOVERED',receipts_with_identity=[x['attempt'] for x in hits],receipts_total=len(cands[m]))
json.dump(out,open(outp,'w'),indent=1); print(json.dumps({m:v['status'] for m,v in out.items()}))
