"""Pin SAME audited closure, frozen graphs, tools and retained exports; clean owned outputs."""
from pathlib import Path
import json,lzma,hashlib,os,shutil,subprocess
B=Path.cwd();H=lambda p:hashlib.sha256(p.read_bytes()).hexdigest();C=Path('/home/dombarker/project-offloads/codex-cx-slice-d-prepared-cache-20261104/NKD_20261108/NKD_exports_20261108');C.mkdir(exist_ok=True)
config=json.loads((B/'NKD_PIN_INPUT.json').read_text());prior=Path(config['predecessor_path']);assert H(prior)==config['predecessor_sha256'];previous=json.loads(lzma.decompress(prior.read_bytes()))
loaded=[json.loads(l)for l in(B/'NKD_LOADED_scan.jsonl').read_text().splitlines()]
assert all(not r['dangling']and not r['duplicate_owners']and r['imports_match']for r in loaded)
exports=[]
for p in(B/'NKD_objects').rglob('*'):
 if not p.is_file():continue
 q=C/p.relative_to(B/'NKD_objects');q.parent.mkdir(parents=True,exist_ok=True)
 if q.exists():assert H(q)==H(p)
 else:shutil.copy2(p,q)
 exports.append(dict(path=str(q),sha256=H(q),bytes=q.stat().st_size))
paths=os.environ['LEAN_PATH'].split(':');paths=[str(C)]+[p for p in paths if p!=str(B/'NKD_objects')];pins=[]
for row in loaded:
 rel=row['module'].replace('.','/')+'.olean';p=next((Path(root)/rel for root in paths if(Path(root)/rel).is_file()),None);assert p,rel
 for q in[p,Path(str(p)+'.private'),Path(str(p)+'.server'),p.with_suffix('.ir')]:
  if q.is_file():pins.append(dict(module=row['module'],path=str(q),sha256=H(q),bytes=q.stat().st_size))
raw=(json.dumps(dict(LEAN_PATH=paths,selected_objects=pins,modules=len(loaded),scan_pass=True),indent=1)+'\n').encode();(B/'NKD_CLOSURE_PINS.json.xz').write_bytes(lzma.compress(raw));(B/'NKD_CLOSURE_PINS.json.sha256').write_text(hashlib.sha256(raw).hexdigest()+'\n')
def key(x):return(x['module'],next(s for s in['.olean.private','.olean.server','.olean','.ir']if x['path'].endswith(s)))
old={key(x):x for x in previous['selected_objects']};new={key(x):x for x in pins};wrong=[dict(module=k[0],suffix=k[1],old=x,new=new.get(k))for k,x in old.items()if k not in new or new[k]['sha256']!=x['sha256']]
comparison=dict(previous_files=len(old),current_files=len(new),mismatches=wrong,added_files=len(set(new)-set(old)),status='PASS'if not wrong else'FINDING');(B/'NKD_PREDECESSOR_COMPARISON.json').write_text(json.dumps(comparison,indent=1)+'\n');assert not wrong
# Every per-run full metadata graph retained once by content hash, with ALL crate features.
graphs={};index={}
for a in ['NKD_K001','NKD_K007','NKD_K002','NKD_K003','NKD_K004','NKD_K005','NKD_K006']:
 p=B/(a+'-graph.json');check=json.loads((B/(a+'-graph-check.json')).read_text());h=H(p);assert check['graph_sha256']==h
 m=json.loads(p.read_text());assert all('features'in n for n in m['resolve']['nodes']);n='NKD_GRAPH_'+h+'.json'
 if h not in graphs:
  data=p.read_bytes();(B/(n+'.xz')).write_bytes(lzma.compress(data));(B/(n+'.sha256')).write_text(h+'\n');graphs[h]=dict(path=n+'.xz',sha256=h,bytes=len(data),crates=len(m['resolve']['nodes']))
 index[a]=dict(graph_sha256=h,graph_file=n+'.xz',feature_crates=len(m['resolve']['nodes']))
(B/'NKD_GRAPH_INDEX.json').write_text(json.dumps(dict(graphs=graphs,attempts=index),indent=1)+'\n')
toolroot=Path(os.environ['LEAN_SYSROOT']);tools=[]
for p in[toolroot/'bin/lean',toolroot/'bin/lake',toolroot/'bin/leanc',B/'S2W_run_host.py',B/'lean-toolchain',Path('/home/dombarker/.cargo/bin/cargo-kani')]:tools.append(dict(path=str(p),sha256=H(p),bytes=p.stat().st_size))
r=subprocess.run(['/home/dombarker/.cargo/bin/cargo-kani','--version'],capture_output=True,text=True);assert r.returncode==0 and '0.67.0'in r.stdout
(B/'NKD_TOOL_PINS.json').write_text(json.dumps(dict(tools=tools,kani_version=r.stdout.strip(),predecessor_pin=config),indent=1)+'\n')
(B/'NKD_EXPORT.json').write_text(json.dumps(dict(export=str(C),files=exports,bytes=sum(x['bytes']for x in exports),cache_retained=True,consumer_paths=paths),indent=1)+'\n')
removed=[]
for n in ['NKD_target','NKD_native','NKD_tmp']:
 p=B/n
 if p.exists():
  assert not p.is_symlink()and p.resolve().parent==B.resolve()
  size=sum(z.stat().st_size for z in p.rglob('*')if z.is_file());shutil.rmtree(p);removed.append(dict(path=str(p),bytes=size))
assert H(B/'NKD_src/Cargo.lock')=='5782e6a32026fdd95d252d0db7ea20b16716e6deb4f5a397e744886bb6ba22ef'
(B/'NKD_HOST_END.json').write_text(json.dumps(dict(status='PASS',removed_owned_outputs=removed,cache_retained=str(C.parent),exports=len(exports),source_scratch_retained=str(B/'NKD_src'),CARGO_TARGET_DIR=str(B/'NKD_target'),disk=shutil.disk_usage(B)._asdict(),frozen_lock_unchanged=True),indent=1)+'\n')
print(json.dumps(dict(status='PASS_PIN_EXPORT',modules=len(loaded),predecessor_files=len(old),new_files=comparison['added_files'],exports=len(exports))))
