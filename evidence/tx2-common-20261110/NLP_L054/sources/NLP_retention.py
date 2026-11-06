PRIOR={'path': 'evidence/ledger22-20261110/NLO_CLOSURE_PINS.json.xz', 'host_path': '/home/dombarker/project-offloads/codex-cx-ledger22-20261110/NLO_CLOSURE_PINS.json.xz', 'sha256': 'f4174c9e947b90af17e19e7d8a153a560559133efa4778260ba1846a03ff7d60', 'bytes': 1536580}
"""Pin one coherent combined closure and retain own objects; no deletion."""
from pathlib import Path
import os,json,lzma,hashlib,shutil
B=Path.cwd();sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
paths=os.environ['LEAN_PATH'].split(':');loaded=[json.loads(l) for l in (B/'NLP_LOADED_scan.jsonl').read_text().splitlines()]
assert loaded and all(not r['dangling'] and not r['duplicate_owners'] and r['imports_match'] for r in loaded)
pins=[]
for row in loaded:
 rel=row['module'].replace('.','/')+'.olean';p=next((Path(root)/rel for root in paths if (Path(root)/rel).is_file()),None);assert p,rel
 for q in [p,Path(str(p)+'.private'),Path(str(p)+'.server'),p.with_suffix('.ir')]:
  if q.is_file():pins.append(dict(module=row['module'],path=str(q),sha256=sha(q),bytes=q.stat().st_size))
raw=(json.dumps(dict(LEAN_PATH=paths,selected_objects=pins,modules=len(loaded),scan_pass=True),indent=1)+'\n').encode()
(B/'NLP_CLOSURE_PINS.json.xz').write_bytes(lzma.compress(raw,preset=6));(B/'NLP_CLOSURE_PINS.json.sha256').write_text(hashlib.sha256(raw).hexdigest()+'\n')
assert sha(Path(PRIOR['host_path']))==PRIOR['sha256']
prior=json.loads(lzma.decompress(Path(PRIOR['host_path']).read_bytes()))
def key(row):return (row['module'],next(s for s in ['.olean.private','.olean.server','.olean','.ir'] if row['path'].endswith(s)))
old={key(x):x for x in prior['selected_objects']};new={key(x):x for x in pins}
wrong=[dict(module=k[0],suffix=k[1],old=x,new=new.get(k)) for k,x in old.items() if k not in new or new[k]['sha256']!=x['sha256']]
comparison=dict(previous_files=len(old),current_files=len(new),same_predecessor_files=len(old)-len(wrong),mismatches=wrong,added_files=len(set(new)-set(old)),status='PASS' if not wrong else 'FINDING')
(B/'NLP_PREDECESSOR_COMPARISON.json').write_text(json.dumps(comparison,indent=1)+'\n');assert not wrong,[(r['module'],r['suffix']) for r in wrong[:20]]
modules=json.loads((B/'NLP_MODULES.json').read_text());checked=[]
for row in modules:
 p=B/'NLP_generated'/(row['module']+'.lean');assert sha(p)==row['sha256'],p
 receipt=json.loads((B/row['passing_attempt']/'receipt.json').read_text());assert receipt['exit_status']==0 and receipt['module']==row['module']
 original=B/row['passing_attempt']/'sources'/'NLP_generated'/p.name;assert sha(original)==row['sha256'],original
 checked.append(row['module'])
seed=json.loads((B/'NLP_SEED.json').read_text())
for row in seed['seed']:
 p=Path(row['destination']);assert p.stat().st_size==row['bytes'] and sha(p)==row['sha256'],p
exports=B/'NLP_exports_final_20261110';exports.mkdir(exist_ok=True);files=[]
for p in sorted((B/'NLP_objects').rglob('*')):
 if not p.is_file():continue
 q=exports/p.relative_to(B/'NLP_objects');q.parent.mkdir(parents=True,exist_ok=True)
 if q.exists():assert sha(q)==sha(p),q
 else:shutil.copy2(p,q)
 files.append(dict(path=str(q),sha256=sha(q),bytes=q.stat().st_size))
(B/'NLP_EXPORT.json').write_text(json.dumps(dict(export=str(exports),files=files,bytes=sum(r['bytes'] for r in files),cache_retained=True),indent=1)+'\n')
toolroot=Path(os.environ['LEAN_SYSROOT']);tools=[]
for p in [toolroot/'bin/lean',toolroot/'bin/lake',toolroot/'bin/leanc',B/'lean-toolchain',B/'S2W_run_host.py',B/'NLP_retention.py']:
 tools.append(dict(path=str(p),sha256=sha(p),bytes=p.stat().st_size))
(B/'NLP_TOOL_PINS.json').write_text(json.dumps(tools,indent=1)+'\n')
(B/'NLP_target').mkdir(exist_ok=True)
size=sum(p.stat().st_size for p in B.rglob('*') if p.is_file());assert size<30_000_000_000
report=dict(status='PASS',closure_modules=len(loaded),closure_objects=len(pins),unchanged_predecessor_objects=len(old),own_modules_verified=checked,seed_files=len(seed['seed']),seed_bytes=seed['bytes'],export_files=len(files),workspace_bytes=size,free_bytes=shutil.disk_usage(B).free,cache_retained=True,keys_touched=False)
(B/'NLP_RETENTION.json').write_text(json.dumps(report,indent=1)+'\n')
(B/'NLP_CLEANUP.json').write_text(json.dumps(dict(cache_deleted=False,deletions=0,retained_target=True,retained_TMPDIR=True,keys_touched=False),indent=1)+'\n')
print(json.dumps(dict(status='PASS',modules=len(loaded),objects=len(pins),exports=len(files),workspace_bytes=size)))
