from pathlib import Path
import json,re,hashlib,subprocess
D=Path('evidence/pv-b3p6-20261028');O=D/'resume14';L=D/'lean';base='bb12e1b99e63ca6e18a3cb75b646ee8ab159258a'
rows=json.loads((O/'receipt-index.json').read_text());t=json.loads((O/'TALLY-resume14.json').read_text());allowed={'propext','Classical.choice','Quot.sound'}
pattern=r"^'([^'\n]+)' (?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)"
assert len(rows)==t['lean_attempts']<=100
assert sorted(r['attempt']for r in rows)==sorted(t['used_ids'])
assert all(69400<=r['attempt']<=69499 for r in rows)
for row in rows:
 p=O/row['receipt'];r=json.loads(p.read_text());assert r['exit_status']==row['exit']and r['swaps']==0
 assert r['limits']=={'memory.high':str(6*2**30),'memory.max':str(8*2**30),'memory.swap.max':'0','pids.max':'64'}
 assert r['command'][-1]=='7000'
 for gate in ['reservation.json','barrier.json']:assert json.loads((p.parent.parent/gate).read_text())['allowed']is True
 raw=(p.parent.parent/'source.lean').read_bytes();assert hashlib.sha256(raw).hexdigest()==r['source_sha256']==row['source_sha256']
 assert subprocess.check_output(['git','show',r['lean_source_revision']+':'+str(L/(r['module']+'.lean'))])==raw
 if row['exit']==0:
  log=(p.parent/'stdout.log').read_text()+'\n'+(p.parent/'stderr.log').read_text();assert 'sorryAx'not in log
  for v in re.finditer(pattern,log,re.M):assert {x.strip()for x in(v[2]or'').split(',')if x.strip()}<=allowed
admission=json.loads((O/'admission-audit.json').read_text());assert admission['errors']==[]and admission['void_attempts']==[]
m=json.loads((O/'focused-manifest.json').read_text())
for s in m['sources']:assert hashlib.sha256(Path(s['path']).read_bytes()).hexdigest()==s['sha256']
audits=[r for r in rows if r['attempt']>=69497];assert [r['attempt']for r in audits]==[69497,69498,69499]and all(r['exit']==0 for r in audits)
a=next(r for r in rows if r['attempt']==69498);text=(O/a['receipt']).parent.joinpath('stdout.log').read_text();actual=[v[1]for v in re.finditer(pattern,text,re.M)];assert sorted(actual)==sorted(m['new_theorems'])and len(actual)==len(set(actual))
# A failed source hash is never later re-elaborated unchanged in this round.
failed={}
for row in sorted(rows,key=lambda r:r['attempt']):
 assert row['source_sha256']not in failed,(row['attempt'],failed.get(row['source_sha256']))
 if row['exit']!=0:failed[row['source_sha256']]=row['attempt']
assert subprocess.check_output(['git','diff','--name-only',base,'HEAD','--','crates','programs'])==b''
assert json.loads((O/'external-verification-resume14.json').read_text())['mismatches']==[]
assert json.loads((O/'cache-verification-resume14.json').read_text())['mismatches']==[]
native=json.loads((O/'native-receipt-index.json').read_text());assert len(native)<=30
for r in native:assert r['swaps']==0 and r['limits']['memory.swap.max']=='0'and r['limits']['memory.max']==str(8*2**30)
summary=dict(entry=base,lean_attempts=len(rows),pass_count=sum(r['exit']==0 for r in rows),reject_count=sum(r['exit']!=0 for r in rows),native_scopes=len(native),kani_runs=0,audit_theorems=len(actual),axioms='standard only',audits=audits,void_attempts=[],unchanged_failed_resubmissions=[],environment_exception_uses=[],failed_source_guard_sha256=hashlib.sha256(Path('tools/pv-b3p6-20261028/compile_resume14.py').read_bytes()).hexdigest(),source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),shipped_source_changes=[],op227_discharged=False)
(O/'verification-summary.json').write_text(json.dumps(summary,indent=2)+'\n');print(json.dumps({k:v for k,v in summary.items()if k not in ['audits']}))
