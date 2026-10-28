from pathlib import Path
import json,hashlib
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-runjoin31-20261028'
rows=[json.loads(p.read_text()) for p in sorted(E.glob('receipt-*.json'))]
used=[json.loads(p.read_text()) for p in E.glob('used-*.json')]
ref=[p.name for p in E.glob('*refusal*.json')]
assert all(44600<=r['attempt']<=44699 for r in rows+used)
charged=[r for r in rows if r.get('exit') is not None]
result=dict(charged=len(charged),accepted=sum(r['accepted'] for r in charged),rejected=sum(not r['accepted'] for r in charged),remaining=100-len(charged),kani=0,used_ids=sorted(r['attempt'] for r in used),refusals=ref,peak_rss=max((r.get('peak_rss_bytes') or 0 for r in rows),default=0),nonzero_swaps=[r['attempt'] for r in rows if r.get('swaps') not in [0,None]])
(E/'tally.json').write_text(json.dumps(result,indent=2)+'\n')
(E/'receipt-index.tsv').write_text('attempt\ttarget\texit\twall\tpeak_rss\tswaps\tsource_revision\taccepted\n'+''.join('\t'.join(str(r.get(k)) for k in ['attempt','target','exit','wall_seconds','peak_rss_bytes','swaps','source_revision','accepted'])+'\n' for r in rows))
print(json.dumps(result))
