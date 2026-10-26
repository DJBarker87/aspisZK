"""Plan a historical provider profile without editing any proof source."""
from pathlib import Path
import json,subprocess,hashlib,re
O=Path(__file__).parent
rows=json.loads((O.parent/'envj-rebuild-20261026/EJR_all-restored-sources.json').read_text())
rows={r['module']:r for r in rows if r['workspace']=='joint'}
proc=subprocess.Popen(['git','cat-file','--batch'],stdin=subprocess.PIPE,stdout=subprocess.PIPE)
def blob(oid):
 proc.stdin.write((oid+'\n').encode());proc.stdin.flush();h=proc.stdout.readline().split();n=int(h[2]);b=proc.stdout.read(n);proc.stdout.read(1);return b
edges={}
for m,r in rows.items():
 b=blob(r['blob']);assert hashlib.sha256(b).hexdigest()==r['source_sha256']
 s=re.sub(r'/\-.*?\-/','',b.decode(),flags=re.S);s=re.sub(r'--[^\n]*','',s)
 edges[m]=[v.replace('.','/') for ln in s.splitlines() if re.match(r'^\s*(?:public\s+|private\s+)?import\s',ln) for v in re.sub(r'^\s*(?:public\s+|private\s+)?import\s+','',ln).split() if re.fullmatch(r'[\w.]+',v)]
proc.terminate()
memo={};active=set()
def needs(m):
 if m=='R1Z/CertBuildExtracted':return True
 if m in memo:return memo[m]
 if m in active:return False
 active.add(m);memo[m]=any(needs(d) for d in edges.get(m,[]));active.remove(m);return memo[m]
selected=[dict(r,imports=edges[m]) for m,r in rows.items() if needs(m)]
for r in selected:
 if r['module']=='R1Z/CertBuildExtracted':
  r.update(source_sha256='d7e06b9f7a29e903f7cf24c2305b80b91658dc8a86ae6aaaecca8a815f26a776',blob='19e9c5f022b0871be3816c7b50c78e497c8f4cc3',revision='d6dd1ca963c4e1993d2605da15bf26f2588dda7e',bytes=30688)
(O/'EJS_provider-profile-plan.json').write_text(json.dumps(dict(profile='EJS_provider',rows=selected,note='Planned only. Symlink unchanged sources; restore only provider blob. Rebuild the provider-dependent closure sequentially; isolate outputs under an EJS directory, preserve the original selection. No near-match substitution.'),indent=2)+'\n')
print('provider-dependent rows',len(selected))
