"""Revalidate committed sibling data in one private, deduplicated evidence view.
No live peer worktree, no compiler, and no write through predecessor symlinks.
"""
from pathlib import Path
import base64,hashlib,json,lzma,os,sys,subprocess,time,resource,importlib
sys.dont_write_bytecode=True
E=Path(__file__).resolve().parent;R=E.parent.parent
meta=json.loads((E/'NEW_PEER_NEV_ARCHIVE.json').read_text())
data=b''
for p in meta['parts']:
 raw=(E/p['path']).read_bytes();assert hashlib.sha256(raw).hexdigest()==p['sha256'];data+=raw
assert hashlib.sha256(data).hexdigest()==meta['compressed_sha256']
raw=lzma.decompress(data);assert hashlib.sha256(raw).hexdigest()==meta['raw_sha256']
pack=json.loads(raw);assert pack['revision']==meta['revision']
S=Path('/private/tmp/NEW_peer_validate_20261104_'+meta['revision'][:10]);S.mkdir(exist_ok=True)
store=S/'.NEW_blobs';store.mkdir(exist_ok=True)
for blob,item in pack['blobs'].items():
 raw=item['content'].encode() if item['encoding']=='utf8' else base64.b64decode(item['content'])
 assert hashlib.sha256(raw).hexdigest()==item['sha256']
 path=store/blob
 if path.exists():assert path.read_bytes()==raw
 else:path.write_bytes(raw)
for path,item in pack['files'].items():
 target=S/path;target.parent.mkdir(parents=True,exist_ok=True)
 if target.exists() and hashlib.sha256(target.read_bytes()).hexdigest()!=pack['blobs'][item['blob']]['sha256']:
  previous=E/'NEW_PEER_NEV_REPLAY_RECEIPT.json'
  generated=set(json.loads(previous.read_text()).get('writes',[])) if previous.exists() else set()
  assert path in generated,('unexpected immutable input change',path)
  target.unlink() # Only the private generated provenance output is reset.
 if not target.exists():os.link(store/item['blob'],target)
 assert hashlib.sha256(target.read_bytes()).hexdigest()==pack['blobs'][item['blob']]['sha256']
for top in ['design','docs','lean']:
 p=S/top
 if not p.exists() and(R/top).exists():p.symlink_to(R/top,target_is_directory=True)
# Python modules must have a private __file__.resolve() root, while static
# receipt/source data can remain read-only predecessor links.
pyfiles={Path(x) for x in subprocess.check_output(['git','ls-files','*.py'],cwd=R,text=True).splitlines() if (R/x).is_file() and x.startswith('evidence/')}
parents={p for f in pyfiles for p in f.parents}
def mirror(src,dst,rel):
 if dst.is_symlink():dst.unlink()
 dst.mkdir(exist_ok=True)
 for child in src.iterdir():
  cr=rel/child.name;target=dst/child.name
  if child.name=='slice-q-mul3-20261103':continue
  if child.is_dir() and cr in parents:mirror(child,target,cr)
  elif child.is_file() and cr in pyfiles:
   if target.is_symlink():target.unlink()
   if not target.exists():target.write_bytes(child.read_bytes())
   else:assert target.read_bytes()==child.read_bytes()
  elif not target.exists() and not target.is_symlink():target.symlink_to(child,target_is_directory=child.is_dir())
mirror(R/'evidence',S/'evidence',Path('evidence'))
os.environ['GIT_DIR']=subprocess.check_output(['git','rev-parse','--absolute-git-dir'],cwd=R,text=True).strip()
os.environ['GIT_WORK_TREE']=str(R)
P=S/'evidence/slice-q-mul3-20261103'
# Archive inputs are immutable; generated outputs may be replaced privately.
# Unlink before writing so hardlinked duplicates can never alter each other.
old_text=Path.write_text;old_bytes=Path.write_bytes
writes=[]
def guard(p):
 p=Path(p);resolved=p.resolve();assert resolved.is_relative_to(S),('forbidden predecessor write',str(p))
 if p.is_file() and p.stat().st_nlink>1:
  raw=p.read_bytes();p.unlink();old_bytes(p,raw)
 writes.append(str(p.relative_to(S)))
def wt(p,*args,**kw):guard(p);return old_text(p,*args,**kw)
def wb(p,*args,**kw):guard(p);return old_bytes(p,*args,**kw)
Path.write_text=wt;Path.write_bytes=wb
sys.path.insert(0,str(P))
start=time.monotonic();status=1
try:
 # The sibling capsule is materialized by its unchanged importer.
 importer=importlib.import_module('NEV_import_net')
 replay_file=P/'NEV_NET_REPLAY.json'
 capsule=P/'.NEV_net_capsule'
 if capsule.exists() and replay_file.exists():
  cached=json.loads(replay_file.read_text());assert len(cached['outputs'])==2 and all(x['exit']==0 for x in cached['outputs'])
  pins=json.loads((P/'NEV_NET_PROVENANCE.json').read_text())
  for path,pin in pins['files'].items():assert hashlib.sha256((capsule/path).read_bytes()).hexdigest()==pin['sha256']
  for item in cached['outputs']:
   assert hashlib.sha256((capsule/'evidence/slice-q-compose3-20261102'/item['script']).read_bytes()).hexdigest()==item['source_sha256']
  old_text(E/'NEW_PEER_NET_REPLAY.json',json.dumps(cached,indent=1)+'\n')
 else:importer.replay()
 union=importlib.import_module('NEV_union')
 own,oe,base,be,packet=union.inputs()
 out,edges,certs,roots=union.recipes(own,oe,base,be,packet)
 assert union.validate(out,edges,certs,roots,base,be)
 assert out==union.obj(P/'NEV_DERIVED_LEDGER.json')
 assert edges==union.obj(P/'NEV_EDGES.json')
 saved=union.obj(P/'NEV_UNION_CERTIFICATES.json');assert saved==json.loads(json.dumps(dict(edges=certs,rows=roots)))
 result=dict(revision=meta['revision'],rows=['TX1:182','TX2:108'],rows_data=[r for r in out['rows'] if r['row'] in roots],edges=[e for e in edges['edges'] if e['caller']==union.ACC],row_certificates=roots,packet=packet,unchanged_peer_checks=True,writes=writes,private_workspace=str(S),archive_raw_sha256=meta['raw_sha256'])
 old_text(E/'NEW_PEER_NEV_CHECKED.json',json.dumps(result,indent=1)+'\n');status=0
finally:
 use=resource.getrusage(resource.RUSAGE_SELF)
 receipt=dict(target='Unchanged NEV_union inputs/recipes/validate on committed archive',exit_status=status,wall_seconds=time.monotonic()-start,peak_rss_kib=int(use.ru_maxrss/1024),swaps=use.ru_nswap,source_revision=meta['revision'],print_axioms='Inherited standard-only receipt checks replayed; no new Lean scope',writes=writes)
 old_text(E/'NEW_PEER_NEV_REPLAY_RECEIPT.json',json.dumps(receipt,indent=1)+'\n')
