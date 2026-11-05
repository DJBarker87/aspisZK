"""Finish independent Pool cuts serially; never repeat a timed-out family."""
from pathlib import Path
import subprocess,json,sys,time
E=Path(__file__).resolve().parent;sys.dont_write_bytecode=True;sys.path.insert(0,str(E))
from NIE_custody_prepare import prepare as custody
from NIE_creation_prepare import prepare as creation
from NIE_fresh_prepare import prepare as fresh
from NIE_verifier_prepare import prepare as verifier
from NIE_dispatch_prepare import prepare as dispatch
from NIE_count_prepare import prepare as count
from NIE_five_prepare import prepare as five
jobs=[]
for n,control in enumerate(['none','delegate','native','close','delegated','frame'],82):jobs.append((n,'custody',lambda c=control:custody(c),control!='none','vault'))
for base,function in [(88,'create_or_allocate_pda_with_rent'),(94,'create_or_allocate_with_seed_with_rent')]:
 for case in range(3):
  for neg in [False,True]:jobs.append((base+2*case+int(neg),function,lambda f=function,c=case,n=neg:creation(f,c,n),neg,'processor'))
for case in range(3):
 for neg in [False,True]:jobs.append((100+2*case+int(neg),'fresh',lambda c=case,n=neg:fresh(c,n),neg,'processor'))
for n,control in enumerate(['none','reply','flag','borrow','rc','identity'],106):jobs.append((n,'verifier-alias',lambda c=control:verifier(c),control!='none','pair_forest_dispatch'))
for neg in [False,True]:jobs.append((112+int(neg),'dispatcher-postguard',lambda n=neg:dispatch(n),neg,'processor'))
for n,control in enumerate(['none','reply','frame'],114):jobs.append((n,'count',lambda c=control:count(c),control!='none','pair_forest'))
for large in [False,True]:
 for neg in [False,True]:jobs.append((117+2*int(large)+int(neg),'withdrawal-arity',lambda l=large,n=neg:five(l,n),neg,'vault'))
rank=lambda job: (0 if job[1]=='dispatcher-postguard' else 1 if job[1] in ['count','withdrawal-arity','fresh'] else 2 if job[1].startswith('create_or_allocate') else 3 if job[1]=='custody' else 4,job[0])
jobs.sort(key=rank)
start=int(sys.argv[1]) if len(sys.argv)>1 else 82
blocked=set()
for number,family,prepare,neg,module in jobs:
 if number<start:continue
 if family in blocked:
  with (E/'NIE_SKIPPED.jsonl').open('a') as f:f.write(json.dumps(dict(reserved_id=f'NIE_K{number:03}',family=family,reason='family timed out; unchanged controls not launched'))+'\n')
  continue
 a=f'NIE_K{number:03}';prepare()
 with (E/(a+'-client.log')).open('w') as f:r=subprocess.run([sys.executable,str(E/'NIE_kani_run.py'),a,module+'::NIE_native::association'],stdout=f,stderr=subprocess.STDOUT)
 p=E/a/'receipt.json'
 if not p.exists():raise SystemExit('Client failure; details retained: '+a)
 x=json.loads(p.read_text());s=(p.parent/'stdout.log').read_text()
 summary=dict(attempt=a,family=family,expected='FAIL' if neg else 'PASS',exit=x['exit_status'],success='SUCCESSFUL' in s,semantic_failure='VERIFICATION' in s and 'FAILED' in s,timeout='timed out' in s or x['exit_status']==124,compiler='could not compile' in s,wall=x['wall_seconds'])
 with (E/'NIE_CAMPAIGN.jsonl').open('a') as f:f.write(json.dumps(summary)+'\n')
 print(json.dumps(summary),flush=True)
 if summary['timeout']:
  blocked.add(family)
  with (E/'NIE_FAILING_STEP.md').open('a') as f:f.write('\n* '+a+' / '+family+': tool timeout; no credit. Same-family controls are not launched unchanged; proceed to the next independent unit. Full assertion/source/resource information is in the attempt receipt.\n')
  continue
 if summary['compiler'] or summary['success']==neg:raise SystemExit('Review required; no unchanged rerun')
