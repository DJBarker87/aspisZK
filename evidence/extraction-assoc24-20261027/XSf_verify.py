from pathlib import Path
import hashlib,json,re
E=Path(__file__).resolve().parent
errors=[];rows=[];accepted={}
for p in sorted(E.glob('XSf_L*/receipt.json')):
 r=json.loads(p.read_text()); a=r['attempt']; log=(p.parent/'stdout.log').read_text()
 for src,h in r['source_hashes'].items():
  snap=p.parent/'sources'/src
  if not snap.exists() or hashlib.sha256(snap.read_bytes()).hexdigest()!=h:errors.append([a,'source hash',src])
 if r['limits']!={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}:errors.append([a,'limits'])
 admission=json.loads((E/(a+'-reservation.json')).read_text())
 if not admission.get('allowed'):errors.append([a,'refused admission'])
 if r['exit_status']==0:
  if 'error:' in log or 'sorryAx' in log:errors.append([a,'accepted errors or sorryAx'])
  for line in r['print_axioms']:
   if 'depends on axioms:' in line:
    ax=line.split('depends on axioms: ')[1].strip('[]').replace(' ','').split(',')
    if set(ax)-{'propext','Classical.choice','Quot.sound'}:errors.append([a,'axioms',line])
  accepted[r['module']]=a
 rows.append(dict(attempt=a,module=r['module'],exit=r['exit_status'],wall=r['wall_seconds'],rss=int(r['peak_rss_kib']),swaps=int(r['swaps'])))
for m,a in accepted.items():
 src=E/(m+'.lean')
 if src.exists():
  r=json.loads((E/a/'receipt.json').read_text())
  if hashlib.sha256(src.read_bytes()).hexdigest() not in r['source_hashes'].values():errors.append([m,'working source differs from last pass'])
summary=dict(lean_actual=len(rows),pass_count=sum(r['exit']==0 for r in rows),fail_count=sum(r['exit']!=0 for r in rows),kani=0,wall=sum(r['wall'] for r in rows),peak_rss_kib=max([r['rss'] for r in rows],default=0),swaps=sum(r['swaps'] for r in rows),accepted_modules=accepted,attempts=rows,errors=errors)
(E/'XSf_VERIFICATION.json').write_text(json.dumps(summary,indent=2)+'\n')
print(json.dumps({k:v for k,v in summary.items() if k not in ['accepted_modules','attempts']},indent=2))
