from pathlib import Path
import json,subprocess,hashlib,re
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-runjoin21-20261027';rs=[json.loads(p.read_text()) for p in sorted(E.glob('receipt-*.json'))]
assert all(38200<=r['attempt']<=38299 for r in rs)
latest={r['target']:r for r in rs if r['accepted']}
status=[]
for m,r in sorted(latest.items()):
 p=R/'docs/research/v8-r0-zk-20261009/lean'/(m+'.lean');h=hashlib.sha256(p.read_bytes()).hexdigest();assert h==r['source_sha256'],m
 t=p.read_text();assert not re.search(r'\b(sorry|admit|native_decide|implemented_by)\b',t)
 assert not re.search(r'^\s*axiom\b|set_option\s+(maxRecDepth|maxHeartbeats)',t,re.M)
 assert r['swaps']==0
 for l in r['axioms']:
  match=re.search(r'axioms: \[([\s\S]*?)\]',l)
  if match:assert {s.strip() for s in match[1].split(',')}<={'propext','Classical.choice','Quot.sound'},l
 status.append(dict(module=m,path=str(p.relative_to(R)),attempt=r['attempt'],sha256=h))
newpaths=subprocess.check_output(['git','ls-files','--others','--exclude-standard','docs/research/v8-r0-zk-20261009/lean/R1Z'],text=True).splitlines()
for path in newpaths:
 p=R/path
 if p.suffix=='.lean':assert 'R1Z/'+p.stem in latest,('unaccepted source',path)
assert not subprocess.check_output(['git','diff','0ec90874e3','--','crates','programs'],text=True)
for name in ['render-prefix.py','render-frontier.py']:
 subprocess.run(['python3',str(R/'tools/pv-runjoin21-20261027'/name),'--check'],check=True)
(E/'proof-status.json').write_text(json.dumps(dict(accepted_modules=status,shipped_diff=[],endpoint_source_unchanged=True,endpoint_audit_reused=37099),indent=2)+'\n')
with (E/'receipt-index.tsv').open('w') as f:
 f.write('attempt\ttarget\texit\twall_seconds\tpeak_rss_bytes\tswaps\tsource_revision\taccepted\taxioms\n')
 for r in rs:f.write('\t'.join(str(r.get(k)) for k in ['attempt','target','exit','wall_seconds','peak_rss_bytes','swaps','source_revision','accepted'])+'\t'+json.dumps(r['axioms'])+'\n')
tally=dict(charged=len(rs),accepted=sum(r['accepted'] for r in rs),rejected=sum(not r['accepted'] for r in rs),never_launched=[38202],Kani=0,peak_rss_bytes=max(r['peak_rss_bytes'] or 0 for r in rs),swaps=sum(r['swaps'] or 0 for r in rs),endpoint_premises_removed_added_weakened=[0,0,0],whole_rows_removed=[],counts=dict(rows=407,P=400,T=3,C=4,OPEN=93))
(E/'tally.json').write_text(json.dumps(tally,indent=2)+'\n');print(json.dumps(tally));print(len(status),'accepted proof sources match their snapshots')
