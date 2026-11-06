from pathlib import Path
import hashlib,json,shutil,lzma
B=Path(__file__).resolve().parent;D=Path('/home/dombarker/project-offloads/codex-cx-slice-d-prepared-cache-20261104/NJT_Q_exports_20261108');D.mkdir(exist_ok=True)
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest();pins=[]
for p in sorted((B/'NJT_Q_objects').rglob('*')):
 if p.is_file():
  q=D/p.relative_to(B/'NJT_Q_objects');q.parent.mkdir(parents=True,exist_ok=True)
  if q.exists():assert q.read_bytes()==p.read_bytes()
  else:shutil.copyfile(p,q)
  pins.append(dict(source=str(p),path=str(q),sha256=sha(q),bytes=q.stat().st_size))
features={};archives=[]
for a in ['NJT_QK001','NJT_QK002','NJT_QK003']:
 p=B/(a+'-graph.json');x=json.loads(p.read_text());nodes={n['id']:n for n in x['resolve']['nodes']};features[a]=[dict(id=p['id'],name=p['name'],version=p['version'],features=nodes[p['id']]['features']) for p in x['packages']]
 q=B/(a+'-graph.json.xz');q.write_bytes(lzma.compress(p.read_bytes(),preset=6));h=B/(a+'-graph.json.sha256');h.write_text(sha(p)+'\n');archives.append(dict(path=q.name,uncompressed_sha256=sha(p),compressed_sha256=sha(q)))
assert sha(B/'NJT_Q_src/Cargo.lock')=='5782e6a32026fdd95d252d0db7ea20b16716e6deb4f5a397e744886bb6ba22ef'
(B/'NJT_QFEATURES.json').write_text(json.dumps(features));(B/'NJT_QEXPORT.json').write_text(json.dumps(dict(export=str(D),files=pins,total_bytes=sum(p['bytes'] for p in pins),cargo_target_dir=str(B/'NJT_Q_target'),graph_archives=archives,unchanged_frozen_lock=True),indent=2));print('query objects exported and native graph/features pinned')
