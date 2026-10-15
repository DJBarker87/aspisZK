from pathlib import Path
import json,hashlib,tarfile
w=Path('/home/dombarker/project-offloads/aspis-r1-mask-lean432-20261015')
m=json.loads((w/'source-kit/manifest.json').read_text())
modules=['ExtractedMask'+x for x in ['SquareArithmetic','CM31Square','CM31SquareEqMul','QM31Square','QM31SquareExact','Power26','TowerBasisExact','HornerPolynomial']]
assert len(modules)==len(set(modules))==8
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
files=set()
records=[]
for mod in modules:
 ps=list((w/'attempts').glob('*-'+mod.replace('.','_')))
 rs=[(p,json.loads((p/'receipt.json').read_text())) for p in ps if (p/'receipt.json').is_file()]
 green=[(p,r) for p,r in rs if r['exit_status']==0]
 assert len(green)==1,(mod,green)
 p,r=green[0]
 src=Path(r['source_path']);snap=Path(r['snapshot_path']);obj=Path(r['output_path'])
 assert sha(src)==sha(snap)==r['source_sha256']
 assert sha(obj)==r['output_sha256']
 assert r['source_unchanged_after'] and r['process_swaps']==0
 assert len(r['axiom_reports'])==r['axiom_report_count']==snap.read_text().count('#print axioms')
 assert all(set(a['axioms'])<=set(['propext','Classical.choice','Quot.sound']) for a in r['axiom_reports'])
 assert r['cgroup']=={'MemoryHigh':'4G','MemoryMax':'6G','MemorySwapMax':'0','TasksMax':128}
 for d in r['direct_imports']:
  assert sha(Path(d['object_path']))==d['object_sha256']
 for attempt in ps:
  files.update(q for q in attempt.rglob('*') if q.is_file())
 files.add(src)
 for q in [obj,Path(str(obj)+'.private'),Path(str(obj)+'.server'),obj.with_suffix('.ir')]:
  if q.is_file(): files.add(q)
 records.append(r)
for root in ['evidence']:
 files.update(p for p in (w/root).rglob('*') if p.is_file())
files.update(w.glob('environment*.json'))
files.update([w/'run-mask432-one.py',w/'exec-mask432-lean.py'])
summary={'scope':'8 selected-mask square/power/basis-exact/polynomial targets on Lean 4.32; not whole mask or verifier correctness','source_base_revision':m['source_revision'],'target_count':len(records),'axiom_report_count':sum(r['axiom_report_count'] for r in records),'axiom_free_reports':sum(not a['axioms'] for r in records for a in r['axiom_reports']),'max_target_time_rss_kib':max(r['max_rss_kib'] for r in records),'process_swaps':sum(r['process_swaps'] for r in records),'sum_controller_wall_seconds':round(sum(r['controller_elapsed_wall_seconds'] for r in records),3),'green_records':records,'archived_files':[{'path':str(p.relative_to(w)),'sha256':sha(p),'bytes':p.stat().st_size} for p in sorted(files)]}
out=w/'power-basis-summary.json';out.write_text(json.dumps(summary,indent=2)+'\n');files.add(out)
archive=w/'power-basis-evidence-20261016.tar.gz'
assert not archive.exists()
with tarfile.open(archive,'w:gz',compresslevel=6) as t:
 for p in sorted(files):t.add(p,arcname=str(p.relative_to(w)),recursive=False)
print(json.dumps({'target_count':summary['target_count'],'axiom_report_count':summary['axiom_report_count'],'archive_bytes':archive.stat().st_size,'archive_sha256':sha(archive),'summary_sha256':sha(out)}))
