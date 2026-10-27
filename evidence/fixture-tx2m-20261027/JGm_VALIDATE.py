from pathlib import Path
import hashlib,json,re,subprocess
P=Path(__file__).resolve().parent;R=P.parents[1]
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
records=[json.loads(f.read_text()) for f in sorted(P.glob('JGm_TX2_[0-9][0-9][0-9]/receipt.json'))]
accepted={}
for d in records:
 if d['exit_status']!=0:continue
 for name,h in d['source_hashes'].items():
  src=R/'lean'/name
  if src.exists() and sha(src)==h:accepted[name]=d
new=sorted((R/'lean').glob('JGm_*.lean'))
unvalidated=[p.name for p in new if p.name not in accepted]
prohibited={p.name:re.findall(r'\b(?:sorry|admit|native_decide|axiom)\b|set_option\s+(?:maxHeartbeats|maxRecDepth)',p.read_text()) for p in new}
prohibited={p:x for p,x in prohibited.items() if x}
bad_axioms=[]
for d in accepted.values():
 for line in d['print_axioms']:
  if 'sorryAx' in line:bad_axioms.append(line)
summary=dict(attempts=len(records),passes=sum(d['exit_status']==0 for d in records),rejects=sum(d['exit_status']!=0 for d in records),kani=0,wall_seconds=sum(d['wall_seconds'] for d in records),peak_rss_kib=max(int(d['peak_rss_kib']) for d in records),swaps=sum(int(d['swaps']) for d in records),validated={name:dict(attempt=d['attempt'],sha256=d['source_hashes'][name],print_axioms=d['print_axioms']) for name,d in sorted(accepted.items())},unvalidated=unvalidated,prohibited=prohibited,bad_axioms=bad_axioms)
(P/'JGm_VALIDATION.json').write_text(json.dumps(summary,indent=2)+'\n')
(P/'JGm_ATTEMPTS.jsonl').write_text(''.join(json.dumps(d)+'\n' for d in records))
print(json.dumps({k:v for k,v in summary.items() if k!='validated'},indent=2))
