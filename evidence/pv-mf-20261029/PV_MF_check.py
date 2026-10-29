#!/usr/bin/env python3
"""Verify manifest components, git blobs, row witnesses and classified hash comparisons.
Default: repository/receipt integrity. --release-gate additionally requires V346 closed.
Use --host for a fresh admitted/capped rehash of the actual retained binary/ELFs.
"""
import argparse,hashlib,json,lzma,subprocess,sys
from pathlib import Path
D=Path(__file__).resolve().parent
sha=lambda b:hashlib.sha256(b).hexdigest()
def git(*a):return subprocess.check_output(['git',*a])
def load(p):
 x=json.loads((D/p).read_text())
 if isinstance(x,dict) and 'compressed' in x:
  r=x['compressed'];b=(D/r['path']).read_bytes();assert sha(b)==r['sha256'],r['path'];raw=lzma.decompress(b);assert sha(raw)==r['uncompressed_sha256'],r['path'];x=json.loads(raw)
 if isinstance(x,dict) and 'sharded' in x:
  out={} if x['kind']=='dict' else []
  for r in x['sharded']:
   b=(D/r['path']).read_bytes();assert sha(b)==r['sha256'] and len(b)==r['bytes'],r['path']
   data=load(r['path'])
   if isinstance(out,dict):out.update(data)
   else:out.extend(data)
  return out
 return x
def main():
 ap=argparse.ArgumentParser();ap.add_argument('--host',action='store_true');ap.add_argument('--release-gate',action='store_true');a=ap.parse_args();m=load('MANIFEST.json');errors=[];counts={}
 def check(ok,msg):
  if not ok:errors.append(msg)
 for p,r in m['parts'].items():
  b=(D/p).read_bytes();check(sha(b)==r['sha256'] and len(b)==r['bytes'],'part '+p)
 files=load('FILES.json');proc=subprocess.Popen(['git','cat-file','--batch'],stdin=subprocess.PIPE,stdout=subprocess.PIPE)
 def blob(h):
  proc.stdin.write((h+'\n').encode());proc.stdin.flush();hd=proc.stdout.readline().split();assert len(hd)==3,hd;b=proc.stdout.read(int(hd[2]));assert proc.stdout.read(1)==b'\n';return b
 ts={}
 for ln in git('ls-tree','-r',m['release_revision']).decode().splitlines():
  mt,p=ln.split('\t',1);ts[p]=mt.split()[-1]
 for p,r in files.items():
  check(ts.get(p)==r['git_blob'],'release blob '+p);b=blob(r['git_blob']);check(sha(b)==r['sha256'] and len(b)==r['bytes'],'file '+p)
 counts['git_files']=len(files)
 for r in load('BUILD-CONTEXT.json')['files']:
  check(ts.get(r['path'])==r['git_blob'] and sha(blob(r['git_blob']))==r['sha256'],'build context '+r['path'])
 if (D/'SUPPLEMENT.json').exists():
  for p,r in load('SUPPLEMENT.json').items():
   check(ts.get(p)==r['git_blob'],'supplement blob '+p);check(sha(blob(r['git_blob']))==r['sha256'],'supplement digest '+p)
 for r in load('build-inputs.json'):
  check(ts.get(r['path'])==r['git_blob'],'build blob '+r['path']);check(sha(blob(r['git_blob']))==r['sha256'],'build digest '+r['path'])
 rc=m['recount9'];b=git('show',rc['revision']+':'+rc['path']);check(sha(b)==rc['sha256'],'recount9 input');check(git('rev-parse',rc['revision']+':'+rc['path']).decode().strip()==rc['git_blob'],'recount9 blob')
 for row in load('RECOUNT9.json'):
  for w in row['witnesses']:
   if w.get('recorded_blob') and w.get('recorded_sha256'):check(sha(blob(w['recorded_blob']))==w['recorded_sha256'],'historical witness '+row['id']+' '+w['path'])
 for r in load('HASH-CLAIMS.json'):
  actual=files[r['path']]
  if 'recorded_sha256' in r:check(r['release_sha256']==actual['sha256'],'claim current hash');same=r['recorded_sha256']==actual['sha256']
  else:check(r['release_git_blob']==actual['git_blob'],'claim current blob');same=r['recorded_git_blob']==actual['git_blob']
  check((r['status']=='IDENTICAL')==same,'comparison status '+r['path'])
 for p,x in load('MODULES.json').items():
  check(p in files,'module unpinned '+p)
  for imp in x['imports']:
   for q in imp['candidates']:check(q in load_modules,'closure candidate missing '+q)
 if (D/'SOURCE-BINDINGS.json').exists():
  for r in load('SOURCE-BINDINGS.json'):
   source=blob(r['source']['git_blob']);span=b''.join(source.splitlines(keepends=True)[r['span']['first_line']-1:r['span']['last_line']])
   check(sha(source)==r['source']['sha256'],'structured source '+r['function'])
   check(sha(blob(r['model']['git_blob']))==r['model']['sha256'],'structured model '+r['function'])
   if r['identity_status']=='IDENTICAL':check(sha(span)==r['span']['sha256'],'structured span '+r['function'])
 counts['modules']=len(load_modules)
 head_tree={}
 for ln in git('ls-tree','-r','HEAD').decode().splitlines():
  mt,path=ln.split('\t',1);head_tree[path]=mt.split()[-1]
 for p in set(load_modules)|{r['path'] for r in load('build-inputs.json')}:
  check(head_tree.get(p)==ts.get(p),'HEAD differs from released proof/build source '+p)
 dirty=set(git('diff','--name-only').decode().splitlines())|set(git('diff','--cached','--name-only').decode().splitlines())
 check(not dirty.intersection(set(load_modules)|{r['path'] for r in load('build-inputs.json')}),'uncommitted release-source change')
 if (D/'BINDING-MODULES.json').exists():
  bindings=load('BINDINGS.json')
  for p,h in load('BINDING-MODULES.json').items():
   check(files[p]['git_blob']==h,'model source '+p)
   # Some generated modules contain only types/traits and no executable def.
   for r in bindings.get(h,[]):
    for f in r['release_source_candidates']:
     check(files[f['path']]['git_blob']==f['git_blob'] and files[f['path']]['sha256']==f['sha256'],'binding source '+f['path'])

 artifacts=load('artifacts.json') if (D/'artifacts.json').exists() else []
 check(len(artifacts)==4,'missing artifact receipt')
 for r in artifacts:check(r['sha256']==r['expected'] and r['matches'],'artifact comparison '+r['name'])
 if a.host:
  p=subprocess.run(['ssh','dombarker@100.108.41.90','python3 /home/dombarker/project-offloads/codex-pv-mf-20261029/PV_MF_rehash.py'],capture_output=True,text=True)
  check(p.returncode==0,'fresh capped host rehash failed: '+str(p.returncode))
  if p.returncode==0:
   try:
    fresh=json.loads(p.stdout.strip().splitlines()[-1]);actual={r['name']:r for r in fresh['artifacts']}
    for r in artifacts:check(actual[r['name']]['sha256']==r['expected'] and actual[r['name']]['bytes']==r['bytes'],'fresh artifact '+r['name'])
   except (ValueError,KeyError,IndexError):check(False,'invalid host hash receipt')
 counts['artifact_mode']='fresh capped host hashes' if a.host else 'recorded native scope receipt; actual host files NOT freshly rehashed'
 stale=load('STALE.json');gaps=load('GAPS.json');claims=load('HASH-CLAIMS.json')
 check(len(stale)==m['counts']['stale_association_records'],'stale count')
 check(len(gaps)==m['counts']['inventory_function_keys'],'inventory count')
 check(len(claims)==m['counts']['file_hash_claims'],'hash-claim count')
 if a.release_gate:
  check(m['status']=='CLOSED','V346 remains '+m['status'])
  check(not stale,'stale associations remain: '+str(len(stale)))
  check(not any(r['status']=='NO_EXACT_DISCOVERED_FUNCTION_ASSOCIATION' for r in gaps.values()),'inventory functions without exact associations remain')
  check(not any(len(i['candidates'])!=1 for r in load_modules.values() for i in r['imports']),'unresolved or ambiguous import cohort remains')
  check(not any(r['binding_status'].startswith('UNVERIFIED') for r in load_modules.values()),'unverified module-to-source associations remain')
  check(not m['release_gate']['unsatisfied'],'named release obligations remain: '+', '.join(m['release_gate']['unsatisfied']))
 result={'integrity':'PASS' if not errors else 'FAIL','V346':m['status'],'counts':counts,'errors':errors};print(json.dumps(result,indent=2));return bool(errors)
load_modules=load('MODULES.json') if (D/'MODULES.json').exists() else {}
if __name__=='__main__':sys.exit(main())
