from pathlib import Path,PurePosixPath
import subprocess,json,hashlib,posixpath
E=Path(__file__).resolve().parent
cache={}
def read(path):
 path=str(path)
 if path in cache:return cache[path]
 p=Path(path)
 if p.is_file():raw=p.read_bytes()
 else:raw=subprocess.check_output(['git','show','HEAD:'+path],stderr=subprocess.DEVNULL)
 # Historical receipt snapshots are content-addressed symlinks in Git.
 if len(raw)<400 and raw.startswith(b'../') and b'\n'not in raw.strip():
  link=raw.decode().strip();raw=read(posixpath.normpath(posixpath.join(posixpath.dirname(path),link)))
 if len(raw)<2_000_000:cache[path]=raw
 return raw
def J(p):return json.loads(read(p))
base=J('evidence/terminal3-20261108/NJX_NATIVE_PAIRS.json');pairs=[]
for row in base['pairs']:
 d='evidence/'+row['evidence'].split('/evidence/',1)[1]
 pairs.append((d,row['positive'],row['negative']))
pairs.append(('evidence/terminal2-20261108','NJL_K059','NJL_K060'))
pairs +=[(str(E.relative_to(Path.cwd())),f'NKI_K{k:03}',f'NKI_K{k+1:03}') for k in [1,3,5,9,11] if (E/f'NKI_K{k+1:03}'/'receipt.json').is_file()]
rows=[]
for d,a,b in pairs:
 r=[J(f'{d}/{x}/receipt.json')for x in[a,b]]
 stdout=[read(f'{d}/{x}/stdout.log').decode()for x in[a,b]]
 graph=[J(f'{d}/{x}-graph-check.json')for x in[a,b]];locks=[J(f'{d}/{x}-lock-check.json')for x in[a,b]]
 assert r[0]['exit_status']==0 and r[1]['exit_status']!=0,(a,b)
 assert 'VERIFICATION:- SUCCESSFUL'in stdout[0] and 'VERIFICATION:- FAILED'in stdout[1],(a,b)
 assert all('one or more unwinding failures'not in s and 'VERIFICATION:- TIMEOUT'not in s for s in stdout),(a,b)
 assert all(x['graph_matches_frozen']for x in graph)and all(x['unchanged']for x in locks),(a,b)
 diff=[n for n in set(r[0]['source_hashes'])|set(r[1]['source_hashes'])if r[0]['source_hashes'].get(n)!=r[1]['source_hashes'].get(n)]
 assert not diff or(a=='NJB_K098'and set(diff)=={'NJB_SOURCE_PINS.json','NJB_install_windowed_gate.py'}),(a,b,diff)
 checked=[]
 for x,rc in zip([a,b],r):
  for n,h in rc['source_hashes'].items():
   path=f'{d}/{x}/sources/{n}'
   try:raw=read(path)
   except subprocess.CalledProcessError:raw=read(f'{d}/{n}');path=f'{d}/{n}'
   assert hashlib.sha256(raw).hexdigest()==h,(x,n,path)
   checked.append(dict(path=path,sha256=h,bytes=len(raw)))
 rows.append(dict(positive=a,negative=b,positive_exit=r[0]['exit_status'],negative_exit=r[1]['exit_status'],same_name=True,frozen_graph=True,offline=True,lock_unchanged=True,unwinding_failure=False,source_hashes_verified=checked,reviewed_first_install=(a=='NJB_K098')))
kmx=hashlib.sha256(read(str(E.relative_to(Path.cwd()))+'/NKI_KMX.patch')).hexdigest();assert kmx=='bcdf749b78eb6143789500d98d64ec3d407b8a17a6d1290c70c822473e8e9a67'
(E/'NKI_NATIVE_PAIRS.json').write_text(json.dumps(dict(pairs=rows,kmx_patch_sha256=kmx,all_pairs_checked=True,source='immutable HEAD blobs and own retained receipts; no sibling worktree access'),indent=1))
print('Native pairs and immutable source hashes verified:',len(rows))
