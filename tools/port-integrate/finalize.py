#!/usr/bin/env python3
from pathlib import Path
import csv,hashlib,json,re,subprocess
R=Path(__file__).resolve().parents[2]; P=R/'docs/research/100bit-spend-path-20261013'; E=P/'evidence/port-integrate-20261021'
p=json.loads((E/'plan.json').read_text()); m=json.loads((E/'manifest.json').read_text()); audit=json.loads((E/'audit.json').read_text()); status=json.loads((E/'run-status.json').read_text())
rows={a['module']:a for a in m['attempts']}; allowed={'propext','Classical.choice','Quot.sound'}; issues=[]
for name in p['compile_order']:
 a=rows.get(name)
 if not a or a['exit']!=0:issues.append(name+' missing or failed');continue
 src=P/'lean'/(name+'.lean')
 assert hashlib.sha256(src.read_bytes()).hexdigest()==a['source_sha256']
 assert a['source_revision']==p['source_revision']
 for report in a['axioms']:
  if 'depends on axioms:' in report:
   used=set(re.search(r'\[([\s\S]*?)\]',report)[1].replace('\n','').replace(' ','').split(','))
   if not used<=allowed:issues.append(report)
 if a['swaps']:issues.append(name+' swapped')
 for d in a['direct_imports']:
  assert hashlib.sha256(Path(d['path']).read_bytes()).hexdigest()==d['sha256']
# Protect all original modules plus all shipped/candidate files, including additions.
protected=subprocess.check_output(['git','diff','--no-renames','--name-status',p['research_revision'],'--','crates','lean-candidate','*/lean-candidate/*'],cwd=R,text=True).splitlines()
existing=subprocess.check_output(['git','diff','--no-renames','--name-status','--diff-filter=MDRT',p['research_revision']],cwd=R,text=True).splitlines()
if protected or existing:issues+=protected+existing
current_research=subprocess.check_output(['git','rev-parse','research'],cwd=R,text=True).strip()
shared_differences=subprocess.check_output(['git','diff','--no-renames','--name-status','--diff-filter=M',current_research,'HEAD','--','*.lean','crates','lean-candidate','*/lean-candidate/*'],cwd=R,text=True).splitlines()
if shared_differences:issues+=shared_differences
movement=subprocess.check_output(['git','diff','--no-renames','--name-status',p['research_revision'],current_research],cwd=R,text=True).splitlines()
(E/'research-movement.json').write_text(json.dumps(dict(pinned_research=p['research_revision'],current_research=current_research,changes_since_pin=movement,shared_protected_file_differences=shared_differences),indent=2)+'\n')
if not audit['pass_scan']:issues.append('forbidden scan failed')
summary=dict(source_revision=p['source_revision'],research_revision=p['research_revision'],current_research_revision=current_research,shared_protected_file_differences=shared_differences,compiled_modules=len(rows),planned_modules=len(p['compile_order']),failed=status['failed'],blocked=status['blocked'],issues=issues,pass_gate=not issues and not status['failed'] and not status['blocked'],wall_seconds=sum(a['wall_seconds'] for a in rows.values()),peak_rss_bytes=max(a['peak_rss_bytes'] for a in rows.values()),swaps=sum(a['swaps'] for a in rows.values()),headline_axioms=rows.get('OraclePortFrozenOrderHeadline',{}).get('axioms',[]),preexisting_changes=existing,shipped_candidate_changes=protected,targets=[dict(module=n,status='PASS' if n in rows and rows[n]['exit']==0 else 'FAIL',**{k:rows[n][k] for k in ['exit','wall_seconds','peak_rss_bytes','swaps','axioms'] if n in rows}) for n in p['targets']])
(E/'summary.json').write_text(json.dumps(summary,indent=2)+'\n')
with (E/'targets.csv').open('w') as f:
 w=csv.writer(f,lineterminator="\n");w.writerow(['module','exit','wall_seconds','peak_rss_bytes','swaps'])
 for name in p['compile_order']:
  a=rows.get(name,{})
  w.writerow([name]+[a.get(k,'blocked') for k in ['exit','wall_seconds','peak_rss_bytes','swaps']])
print(json.dumps(summary,indent=2))
