from pathlib import Path
import hashlib,json,re
E=Path(__file__).resolve().parent
attempts=[];selected={};failures=[]
for d in sorted(E.glob('XSc_L[0-9][0-9][0-9]')):
 p=d/'receipt.json'
 if not p.exists():continue
 r=json.loads(p.read_text());attempts.append(r)
 if r['exit_status']!=0:failures.append(r['attempt']);continue
 for source,digest in r['source_hashes'].items():
  name=Path(source).name;local=E/name
  if not local.exists():local=E/'XSc_dependencies'/(name+'.txt')
  if not local.exists():continue
  if hashlib.sha256(local.read_bytes()).hexdigest()!=digest:continue
  if name=='XSc_QueryNext.lean':continue # duplicate XRr fact, explicitly excluded
  axes=r.get('print_axioms',[])
  if any('sorryAx' in a for a in axes):raise SystemExit('rejected axioms in '+str(p))
  for a in axes:
   m=re.search(r'axioms: \[(.*)\]',a)
   if m and not set(m[1].split(', '))<={'propext','Classical.choice','Quot.sound'}:raise SystemExit(a)
  selected[name]={'attempt':r['attempt'],'source_sha256':digest,'axes':axes}
current=[p.name for p in E.glob('XSc_*.lean')]
report={'compiler_runs':len(attempts),'passed':sum(r['exit_status']==0 for r in attempts),'failed':failures,
 'conservative_slots':len(list(E.glob('XSc_L[0-9][0-9][0-9].json'))),
 'kani_runs':0,'selected_current_sources':selected,'uncompiled_or_excluded':[p for p in current if p not in selected],
 'aggregate_wall_seconds':sum(float(r['wall_seconds']) for r in attempts),
 'peak_rss_kib':max((int(r['peak_rss_kib']) for r in attempts),default=0),
 'swaps':sum(int(r['swaps']) for r in attempts),'full_release_manifest':False}
(E/'XSc_VERIFICATION.json').write_text(json.dumps(report,indent=2)+'\n')
(E/'XSc_attempts.jsonl').write_text(''.join(json.dumps(r)+'\n' for r in attempts))
print(json.dumps({k:v for k,v in report.items() if k not in ('selected_current_sources','uncompiled_or_excluded')},indent=2))
