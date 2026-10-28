"""Offline evidence checks, not a Lean replay."""
from pathlib import Path
import json,hashlib,re
E=Path(__file__).resolve().parent;R=E.parents[1]
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
rows=json.loads((E/'NDO_RETARGET_SOURCES.json').read_text())
for r in rows:assert sha(R/r['path'])==r['retarget_sha256'],r['module']
dup=json.loads((E/'NDO_DUPLICATES.json').read_text());assert len(dup['pairs'])==2922
assert sum(not p['identical_after_module_import_rename'] for p in dup['pairs'])==70
assert sum(not p['body_equal_ignoring_comments_whitespace_imports'] for p in dup['pairs'])==23
attempts=[json.loads(p.read_text()) for p in sorted(E.glob('NDO_L*/receipt.json'))]
assert len(attempts)<=60 and len({r['module'] for r in attempts})==len(attempts)
summary=[]
for r in attempts:
 assert r['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
 assert '-M7000' in r['command'] and r['swaps']=='0'
 ad=json.loads((E/(r['attempt']+'-reservation.json')).read_text());assert ad['allowed'] is True
 admissions=[json.loads(l) for l in (E/'NDO_ATTEMPTS.jsonl').read_text().splitlines() if l]
 assert any(x.get('kind')=='admission' and x['attempt']==r['attempt'] and x['exit_status']==0 and x['allowed'] for x in admissions)
 for path,h in r['source_hashes'].items():assert sha(E/r['attempt']/'sources'/path)==h
 if r['exit_status']==0:
  assert not any('sorryAx' in s for s in r['print_axioms'])
  for s in r['print_axioms']:
   for n in re.findall(r'\[([^\]]*)\]',s):
    assert all(x.strip() in ['propext','Classical.choice','Quot.sound'] for x in n.split(',')),s
 summary.append({k:r[k] for k in ['attempt','module','exit_status','wall_seconds','peak_rss_kib','swaps','source_revision','source_hashes','print_axioms']})
assert not list(E.rglob('*.olean'))
assert not [p for p in E.rglob('*') if p.is_file() and p.stat().st_size>20*1024*1024]
result=dict(validation='PASS: offline source/evidence consistency only',duplicate_pairs=2922,nonidentical_pairs=70,substantive_phase_pairs=23,prepared_witness_modules=len(rows),normal_attempts=len(attempts),passing_attempts=sum(r['exit_status']==0 for r in attempts),rejected_attempts=sum(r['exit_status']!=0 for r in attempts),agg16_attempts=0,combined_replay='NOT RUN: unchanged statement type mismatch and 3118-module rebuild exceeds 60-attempt ceiling',compiled_witness_modules=[r['module'] for r in attempts if r['exit_status']==0 and r['module'] in {x['module'] for x in rows}],attempts=summary)
(E/'NDO_VERIFICATION.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({k:v for k,v in result.items() if k not in ['attempts','compiled_witness_modules']}))
