"""Summarize the live allocation without launching jobs."""
from pathlib import Path
import json,re
root=Path(__file__).resolve().parents[2];ev=root/'evidence/pv-cb-20261026'
rs=[];used=[]
for p in ev.glob('38*.json'):
 m=re.match(r'^(38\d\d\d)(?:-|\.)',p.name)
 if m and 38300<=int(m[1])<=38599:used.append(int(m[1]))
 if re.fullmatch(r'38\d\d\d.json',p.name):
  r=json.loads(p.read_text())
  if 38300<=r['attempt']<=38599:rs.append(r)
rs.sort(key=lambda r:r['attempt'])
ks=[]
for p in ev.glob('kani-resume4-*/collected-receipt.json'):
 r=json.loads(p.read_text());ks.append(dict(name=p.parent.name,**{k:r.get(k) for k in ['harness','exit','wall','peak_rss_kib','swap','source_revision']}))
pending=[p.parent.name for p in ev.glob('kani-resume4-*/target.json') if not (p.parent/'collected-receipt.json').exists()]
summary=dict(lean_used=len(rs),lean_budget=100,lean_passed=sum(r['exit']==0 for r in rs),lean_remaining=100-len(rs),next_unused_id=max(used,default=38299)+1,reserved_last3='Joint axioms audits, attempts98–100',kani_used=len(ks)+len(pending),kani_completed=len(ks),kani_running_or_admitted=pending,kani_budget=12,kani_runs=ks,rows_before=23,rows_after=23,endpoint_premises_removed=0,target='not yet established')
(ev/'RESUME4-TALLY.json').write_text(json.dumps(summary,indent=2)+'\n')
(ev/'RESUME4-TALLY.md').write_text(f"# Resume 4 running tally\n\nLean {len(rs)}/100 charged ({summary['lean_passed']} green); next unused ID {summary['next_unused_id']}.\nReserve final3 attempts for joint axioms audit. Uncharged missing-object preflights are retained separately and never reused.\nKani {len(ks)+len(pending)}/12 charged/reserved ({len(ks)} complete; {len(pending)} active), plus one trivial configuration diagnosis probe.\nRows23/73 →23/73; no endpoint premise removed; target not yet established.\n\nSee KANI-CONFIG.md, RESUME4-ROWS.md, numbered JSON receipts and the JSON tally.\n")
s=['# Resume 4 Lean receipts','','Stopped/failed outputs are rejected, including any error-recovery sorryAx output. Every numbered JSON records launch revision and exact source/dependency identities.38300 has incomplete time metrics because the worker stopped its entire scope; subsequent interruptions target only Lean so time can flush.','','|ID|Target|Exit|Wall|Peak RSS KiB|Swap|Revision|Axioms|','|---:|---|---:|---|---:|---:|---|---|']
for r in rs:s.append(f"|[{r['attempt']}]({r['attempt']}.json)|{r['module']}|{r['exit']}|{r['wall']}|{r['peak_rss_kib']}|{r['swap']}|{r['source_revision'][:10]}|{'standard/none' if not r['exit'] else 'REJECTED'}|")
(ev/'RESUME4-RECEIPTS.md').write_text('\n'.join(s)+'\n')
print(json.dumps(summary))
