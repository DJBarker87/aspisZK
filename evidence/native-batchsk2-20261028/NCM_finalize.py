"""Own read-only receipt/source validation and one final focused audit source."""
from pathlib import Path
import hashlib,json,re,subprocess
E=Path(__file__).resolve().parent;R=E.parents[1];L=R/'docs/research/100bit-spend-path-20261013/lean'
records=[json.loads(line) for line in (E/'NCM_ATTEMPTS.jsonl').read_text().splitlines() if line.strip()]
slots={r['attempt'] for r in records if r.get('kind')=='lean'}
assert len(slots)<=80
assert len({r['attempt'] for r in records if r.get('kind')=='kani'})<=50
accepted={};drafts={};roots=[]
for p in sorted(L.glob('NCM_*.lean')):
 data=p.read_bytes();sha=hashlib.sha256(data).hexdigest()
 hits=[r for r in records if r.get('exit_status')==0 and sha in r.get('source_hashes',{}).values()]
 item=dict(source=str(p.relative_to(R)),sha256=sha,size=len(data))
 if hits:
  item.update(attempt=hits[-1]['attempt'],axioms=hits[-1]['print_axioms'])
  assert all('sorryAx' not in a for a in item['axioms'])
  accepted[p.stem]=item
  ns=re.search(r'^namespace (AspisR1\.NCM_[A-Za-z0-9_]+)',data.decode(),re.M)
  if ns:roots.extend(ns[1]+'.'+n for n in re.findall(r'^theorem ([A-Za-z0-9_]+)',data.decode(),re.M))
 else:drafts[p.stem]=item
 assert not re.search(r'^\s*(axiom|sorry|admit)\b|\bnative_decide\b|set_option\s+(maxRecDepth|maxHeartbeats)',data.decode(),re.M),p
assert not any(p.stat().st_size>20*1024*1024 for p in E.rglob('*') if p.is_file())
report=dict(lean_slots=len(slots),kani_runs=len({r['attempt'] for r in records if r.get('kind')=='kani'}),accepted=accepted,unvalidated=drafts,roots=sorted(set(roots)),shipped_equal_frozen=subprocess.run(['git','diff','--quiet','4bb3b3f5','--','crates','programs'],cwd=R).returncode==0)
(E/'NCM_SOURCE_VALIDATION.json').write_text(json.dumps(report,indent=2)+'\n')
modules=[m for m in accepted if m!='NCM_Audit']
audit='import NCE_Statements\n'+''.join('import '+m+'\n' for m in modules)+'\n-- One focused union audit, not a deployed headline replay.\n'+''.join('#print axioms '+root+'\n' for root in sorted(set(roots)))
(L/'NCM_Audit.lean').write_text(audit)
print(json.dumps({k:report[k] for k in ['lean_slots','kani_runs','shipped_equal_frozen']}))
print('accepted',len(accepted),'unvalidated',list(drafts),'roots',len(set(roots)))
