"""Receipt inventory; does not launch Lean or change build infrastructure."""
from pathlib import Path
import hashlib,json,re
P=Path(__file__).resolve().parent;R=P.parents[1]
rows=[];valid={}
for p in sorted(P.glob('JGv_TX2_[0-9][0-9][0-9]/receipt.json')):
 d=json.loads(p.read_text());rows.append(d)
 if d['exit_status']==0:
  for name,sha in d['source_hashes'].items():
   src=R/'lean'/name
   if src.exists() and hashlib.sha256(src.read_bytes()).hexdigest()==sha:
    axs=d['print_axioms']
    assert axs and all(not any(x in s for x in ['sorryAx','[step','axioms: [source']) for s in axs),p
    for s in axs:
     m=re.search(r'depends on axioms: \[(.*)\]',s)
     if m: assert set(m.group(1).split(', ')) <= {'propext','Classical.choice','Quot.sound'},s
    theorems=re.findall(r'^(?:theorem|lemma)\s+(\w+)',src.read_text(),re.M)
    for th in theorems:assert any('.'+th+"'" in a for a in axs),(p,th)
    valid[name]=dict(attempt=d['attempt'],sha256=sha,print_axioms=axs)
(P/'JGv_ATTEMPTS.jsonl').write_text(''.join(json.dumps(d,sort_keys=True)+'\n' for d in rows))
(P/'JGv_VALIDATION.json').write_text(json.dumps(valid,indent=2)+'\n')
summary=dict(processes=len(rows),passed=sum(d['exit_status']==0 for d in rows),rejected=sum(d['exit_status']!=0 for d in rows),kani=0,total_wall=sum(d['wall_seconds'] for d in rows),maximum_rss_kib=max(int(d['peak_rss_kib']) for d in rows),swaps=sum(int(d['swaps']) for d in rows),checked_current_sources=len(valid))
(P/'JGv_SUMMARY.json').write_text(json.dumps(summary,indent=2)+'\n');print(summary)
