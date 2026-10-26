from pathlib import Path
import json,hashlib,re
P=Path(__file__).resolve().parent;R=P.parents[1]
rows=[];valid={};records=[]
for d in sorted(P.glob('JFr_TX2_[0-9][0-9][0-9]')):
 p=d/'receipt.json'
 if not p.exists():continue
 x=json.loads(p.read_text());a=x['attempt'];r=dict(attempt=a,target=x['sources'],exit=x['exit_status'],wall=x['wall_seconds'],rss=int(x['peak_rss_kib']),swap=int(x['swaps']),revision=x['source_revision'],source_hashes=x['source_hashes'],axioms=x['print_axioms']);rows.append(r)
 for f in sorted(d.rglob('*')):
  if f.is_file():records.append(dict(path=str(f.relative_to(P)),bytes=f.stat().st_size,sha256=hashlib.sha256(f.read_bytes()).hexdigest()))
 if x['exit_status']!=0:continue
 assert x['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'},a
 assert int(x['swaps'])==0,a
 for l in x['print_axioms']:
  if 'depends on axioms:' in l:
   names=set(re.search(r'\[([^]]*)\]',l)[1].replace(' ','').split(','))
   assert names<={'propext','Classical.choice','Quot.sound'},(a,l)
 for file,sha in x['source_hashes'].items():
  f=R/'lean'/file
  if not f.exists() or hashlib.sha256(f.read_bytes()).hexdigest()!=sha:continue
  text=f.read_text();namespace=re.search(r'^namespace ([\w.]+)',text,re.M)[1]
  for name in re.findall(r'^(?:private )?theorem ([\w.]+)',text,re.M):
   assert any("'"+namespace+'.'+name+"'" in line for line in x['print_axioms']),(a,name)
  assert not re.search(r'\b(sorry|admit|native_decide)\b|^axiom\s|set_option\s+(maxRecDepth|maxHeartbeats)',text,re.M),file
  valid[file]=dict(attempt=a,sha256=sha)
(P/'JFr_TX2_VALIDATION.json').write_text(json.dumps(valid,indent=2)+'\n')
(P/'JFr_TX2_RECORDS_MANIFEST.json').write_text(json.dumps(records,indent=2)+'\n')
(P/'JFr_TX2_SUMMARY.json').write_text(json.dumps(dict(lean_processes=len(rows),passed=sum(x['exit']==0 for x in rows),rejected=sum(x['exit']!=0 for x in rows),wall_seconds=sum(x['wall'] for x in rows),maximum_rss_kib=max((x['rss'] for x in rows),default=0),swaps=sum(x['swap'] for x in rows),kani_runs=0,checked_current_sources=len(valid),attempts=rows),indent=2)+'\n')
print(json.dumps(dict(attempts=len(rows),passing=sum(x['exit']==0 for x in rows),checked_sources=len(valid))))
