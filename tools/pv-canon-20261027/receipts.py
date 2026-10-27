from pathlib import Path
import json,re,subprocess,hashlib
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-canon-20261027';rows=[]
for p in sorted(E.glob('*/receipt.json')):
 r=json.loads(p.read_text());tm=r.get('time_log') or '';out=(p.parent/'out.log').read_text()
 rss=re.search(r'Maximum resident set size \(kbytes\):\s*(\d+)',tm);swap=re.search(r'Swaps:\s*(\d+)',tm)
 sets=[re.findall(r'[\w.]+',s) for s in re.findall(r'depends on axioms:\s*\[([^]]*)\]',out,re.S)]
 allowed={'propext','Classical.choice','Quot.sound'}
 row=dict(kind='Lean' if 'attempt' in r else 'Kani',id=r.get('attempt',r.get('number')),target=r['target'],exit=r['exit'],wall_seconds=r['wall_seconds'],peak_rss_kib=int(rss[1]) if rss else None,swap=int(swap[1]) if swap else None,revision=r['revision'],source_sha256=r.get('source_sha256'),receipt=str(p.relative_to(R)),axiom_sets=sets,no_axiom_reports=out.count('does not depend on any axioms'),accepted_axioms=all(set(s)<=allowed for s in sets) if sets or 'does not depend on any axioms' in out else None)
 rows.append(row)
(E/'receipts.jsonl').write_text(''.join(json.dumps(r)+'\n' for r in rows))
lean=[r for r in rows if r['kind']=='Lean'];kani=[r for r in rows if r['kind']=='Kani'];audits=[r for r in lean if r['id']>=44497];assert len(lean)==100 and len(kani)==6;assert len(audits)==3 and all(r['exit']==0 and r['accepted_axioms'] for r in audits);assert all(r['swap']==0 for r in rows)
t=json.loads((E/'tally.json').read_text());assert t['lean']==100 and t['kani']==6
summary=dict(lean_attempts=len(lean),lean_pass=sum(r['exit']==0 for r in lean),lean_fail=sum(r['exit']!=0 for r in lean),kani_runs=len(kani),kani_pass=sum(r['exit']==0 for r in kani),kani_fail=sum(r['exit']!=0 for r in kani),audits=audits,axiom_reports_in_final_audits=sum(len(r['axiom_sets'])+r['no_axiom_reports'] for r in audits),max_successful_lean_rss_kib=max(r['peak_rss_kib'] for r in lean if r['exit']==0),max_lean_rss_kib=max(r['peak_rss_kib'] for r in lean),all_swaps_zero=True,source_base='ea81432954',privacy_target='not yet established',V403='OPEN',endpoint_premises_removed=0)
(E/'FINAL.json').write_text(json.dumps(summary,indent=2)+'\n');print('Lean',len(lean),'Kani',len(kani),'audit reports',summary['axiom_reports_in_final_audits'],'all final audits passed')
