"""Read-only imported-object retention checks plus private owned export."""
from pathlib import Path
import json,hashlib,lzma,shutil,os,re
b=Path.cwd();root=b/'NNH_objects';exports=b/'NNH_exports_continuation_20261111';exports.mkdir(exist_ok=True)
assert shutil.disk_usage(b).free>=40_000_000_000
manifests=[json.loads(lzma.decompress((b/'NNH_CACHE_IMPORTS.json.xz').read_bytes()))['files']]
for n in ['NNH_NND_IMPORTS.json','NNH_SEED_WAdm_Fissioned.json']:
 if (b/n).exists():manifests.append(json.loads((b/n).read_text()))
# Verify every additional retained import, including candidate-only inputs.
for n in ['NNH_RESUME_LIBRARY_IMPORTS.json','NNH_RESUME_DEPENDENCY_IMPORTS.json',
 'NNH_RESUME_FLAT_IMPORTS.json','NNH_LANE_IMPORTS.json',
 'NNH_FINISH_DEPENDENCY_IMPORTS.json','NNH_FINISH_IMPORTS.json','NNH_SEED_NMT_tx1.json']:
 if (b/n).exists():
  data=json.loads((b/n).read_text())
  manifests.append(data['objects'] if isinstance(data,dict) else data)
verified=0
for manifest in manifests:
 for row in manifest:
  p=Path(row['destination']);assert hashlib.sha256(p.read_bytes()).hexdigest()==row['sha256'],str(p)
  verified+=1
source_rows=[];files=[]
# Read each receipt once. The source/object association check stays identical.
receipts=[json.loads(q.read_text()) for q in b.glob('NNH_L*/receipt.json')]
latest={}
for r in sorted(receipts,key=lambda r:r['attempt']):
 if r.get('kind')=='lean' and r['exit_status']==0:latest[r['module']]=r
# Elaboration exit 0 is insufficient: parse the complete multiline axiom audit.
# The superseded native checker branch is retained on disk but never exported.
allowed={'propext','Classical.choice','Quot.sound'}
rejected=[]
for module,r in list(latest.items()):
 log=(b/r['attempt']/'stdout.log').read_text()
 extra=[]
 for match in re.finditer(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]",log,re.S):
  extra.extend(x.strip() for x in match[2].split(',') if x.strip() not in allowed)
 if extra:
  rejected.append(dict(module=module,receipt=r['attempt'],nonstandard_axioms=extra))
  del latest[module]
for module in ['NNH_Stage1ZeroOk']:
 if module in latest:
  rejected.append(dict(module=module,receipt=latest[module]['attempt'],reason='rev2 support alias conflicts with rev3 owner; replaced by NNH_Stage1ZeroCurrent'))
  del latest[module]
for p in sorted((b/'NNH_generated').glob('*.lean')):
 obj=root/(p.stem+'.olean')
 if not obj.exists():continue
 # Export only the exact successful final source/object association.
 if p.stem not in latest:continue
 r=latest[p.stem];expected=r['source_hashes']['NNH_generated/'+p.name]
 assert hashlib.sha256(p.read_bytes()).hexdigest()==expected,str(p)
 source_rows.append(dict(module=p.stem,source=str(p),source_sha256=expected,receipt=r['attempt'],source_revision=r['source_revision']))
 for q in [obj,Path(str(obj)+'.private'),Path(str(obj)+'.server'),obj.with_suffix('.ir')]:
  if not q.exists():continue
  dest=exports/q.name;shutil.copy2(q,dest);h=hashlib.sha256(q.read_bytes()).hexdigest();assert hashlib.sha256(dest.read_bytes()).hexdigest()==h
  files.append(dict(module=p.stem,path=str(dest),sha256=h,bytes=dest.stat().st_size))
# The complete selected search-path object inventory includes unchanged caches;
# it is not represented as a new cold release build or a source-provenance fix.
selected={}
for search in os.environ['LEAN_PATH'].split(':'):
 for p in sorted(Path(search).rglob('*')):
  if not p.is_file() or not any(str(p).endswith(s) for s in ['.olean','.olean.private','.olean.server','.ir']):continue
  rel=str(p.relative_to(search))
  if rel in selected:continue
  selected[rel]=dict(path=str(p),relative=rel,sha256=hashlib.sha256(p.read_bytes()).hexdigest(),bytes=p.stat().st_size)
raw=json.dumps(dict(LEAN_PATH=os.environ['LEAN_PATH'],selected_search_objects=list(selected.values()),sources=source_rows)).encode()
(b/'NNH_CLOSURE_PINS.json.xz').write_bytes(lzma.compress(raw));(b/'NNH_CLOSURE_PINS.json.sha256').write_text(hashlib.sha256(raw).hexdigest()+'\n')
(b/'NNH_EXPORT_REJECTED.json').write_text(json.dumps(rejected,indent=1)+'\n')
(b/'NNH_EXPORT.json').write_text(json.dumps(dict(export=str(exports),files=files,sources=source_rows,prepend_to='NNH_PATHS.json',no_row_credit=True,cold_release_replay=False),indent=1)+'\n')
result=dict(verified_imported_objects=verified,selected_search_objects=len(selected),exported_files=len(files),modules=len(source_rows),disk=shutil.disk_usage(b)._asdict(),wallet_or_key_actions=0,shipped_changes=False)
(b/'NNH_FINAL_HOST.json').write_text(json.dumps(result,indent=1)+'\n');print(json.dumps(result))
