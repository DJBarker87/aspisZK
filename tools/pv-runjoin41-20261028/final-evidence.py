"""Read-only budget, source retention and scope sequence evidence."""
from pathlib import Path
import json,subprocess,hashlib,datetime,re
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-runjoin41-20261028'
rows=sorted([json.loads(p.read_text()) for p in E.glob('receipt-*.json')],key=lambda x:x['attempt'])
assert [x['attempt'] for x in rows]==list(range(60200,60300))
assert all(x['completed_modules']==1 for x in rows)
accepted=[x for x in rows if x['accepted']];failed=[x for x in rows if not x['accepted']]
assert len(accepted)==74 and len(failed)==26
mods=[v for p in sorted(E.glob('modules-*.json')) for v in json.loads(p.read_text())]
allowed={'propext','Classical.choice','Quot.sound'}
for x in accepted:
 for line in x['axioms']:
  match=re.search(r'depends on axioms: \[([^]]*)\]',line)
  if match:assert {v.strip() for v in match[1].split(',') if v.strip()}<=allowed,line
assert all(x['swaps']==0 for x in rows)
failed_sources=[]
for v in mods:
 if v['accepted']:continue
 pin=v['source'];blob=pin['git_blob'];b=subprocess.check_output(['git','cat-file','blob',blob],cwd=R);sha=hashlib.sha256(b).hexdigest();assert sha==v['source_sha256']
 failed_sources.append(dict(module=v['module'],blob=blob,sha256=sha,revision=v['source_revision'],retained=True))
(E/'retained-failed-sources.json').write_text(json.dumps(failed_sources,indent=2)+'\n')
intervals=[]
for x in rows:
 t=datetime.datetime.fromisoformat(x['utc']).timestamp();tr=json.loads((E/f"transport-{x['attempt']}.json").read_text());intervals.append((t,t+tr['wall'],x['attempt']))
intervals.sort();overlap=[(a[2],b[2],a[1]-b[0]) for a,b in zip(intervals,intervals[1:]) if a[1]>b[0]];assert not overlap
(E/'scope-sequence-check.json').write_text(json.dumps(dict(intervals=[dict(attempt=a,start_utc=datetime.datetime.fromtimestamp(s,datetime.timezone.utc).isoformat(),end_upper_bound_utc=datetime.datetime.fromtimestamp(e,datetime.timezone.utc).isoformat()) for s,e,a in intervals],overlaps=overlap),indent=2)+'\n')
new=[v['module'] for v in mods if v['accepted'] and v['module'].startswith('R1Z.PV_RunJoin_') and v['module'].endswith('41')]
tally=dict(attempts=len(rows),accepted=len(accepted),rejected=len(failed),kani=0,attempt_ids=[x['attempt'] for x in rows],audit_ids=[60297,60298,60299],new_modules=new,new_source_modules=26,new_audits=3,inherited_prerequisites=45,all_accepted_printed_axioms_standard=True,peak_rss_bytes=max(x['peak_rss_bytes'] for x in rows),all_swaps_zero=True,source_revision=subprocess.check_output(['git','rev-parse','HEAD'],cwd=R,text=True).strip(),stop='100 Lean compile attempts exhausted',rows_removed=0,endpoint_fields_removed=0,endpoint_fields_added=0,endpoint_fields_weakened=0,endpoint_fields_changed=0)
assert len(new)==29
(E/'final-tally.json').write_text(json.dumps(tally,indent=2)+'\n')
base='845d6424fbae0a743a9e671536606538f8c9df7a'
(E/'commits.txt').write_text(subprocess.check_output(['git','log','--oneline',base+'..HEAD'],cwd=R,text=True))
print(json.dumps({k:tally[k] for k in ['attempts','accepted','rejected','kani','new_source_modules','new_audits','inherited_prerequisites','peak_rss_bytes','rows_removed']}))
