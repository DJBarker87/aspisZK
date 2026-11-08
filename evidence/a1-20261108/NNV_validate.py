"""NNV evidence validation only; this launches no prover or host scope."""
from pathlib import Path
import json,hashlib,re,subprocess
E=Path(__file__).resolve().parent
allowed={'propext','Classical.choice','Quot.sound'}
receipts=[json.loads(p.read_text()) for p in sorted(E.glob('NNV_L[0-9][0-9][0-9]/receipt.json'))]
assert len(receipts)<=100
latest={};failures=[];roots={}
for r in receipts:
 a=r['attempt'];latest[r['module']]=r
 assert r['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
 assert r['timeout']==180 and r['kind']=='lean'
 assert all(flag in r['command'] for flag in ['-j1','-M7000','-DElab.async=false'])
 ad=json.loads((E/(a+'-admission.json')).read_text())
 assert ad['exit']==0 and ad['reservation']['allowed'] is True
 log=(E/a/'stdout.log').read_text()
 if r['exit_status']!=0:
  failures.append({'attempt':a,'module':r['module'],'kernel_memory':'excessive memory consumption' in log,'timeout':r['exit_status']==124})
  continue
 assert 'sorryAx' not in log
 for line in r['print_axioms']:
  if 'depends on axioms:' in line:
   axes=set(re.search(r'\[([^\]]*)\]',line)[1].split(', '))- {''}
   assert axes<=allowed,(a,line)
  roots[re.search(r"'([^']+)'",line)[1]]=line
changes=subprocess.check_output(['git','diff','--name-only','7f6c42c1ee5'],text=True).splitlines()
assert all(p.startswith('evidence/a1-20261108/') for p in changes)
assert not [p for p in E.rglob('*') if p.is_file() and p.stat().st_size>20_000_000]
modules={}
for mod,r in latest.items():
 p=E/(mod+'.lean')
 if r['exit_status']==0 and p.exists():
  source=r['sources'][0]
  assert hashlib.sha256(p.read_bytes()).hexdigest()==r['source_hashes'][source],mod
  modules[mod]={'attempt':r['attempt'],'source_sha256':r['source_hashes'][source],'axioms':r['print_axioms']}
combined=latest.get('NNV_COMBINED_IMPORT')
result={'scope_count':len(receipts),'passes':sum(r['exit_status']==0 for r in receipts),'failures':failures,
 'accepted_current_modules':modules,'standard_only_on_all_passing_receipts':True,
 'combined':None if combined is None else {k:combined[k] for k in ['attempt','exit_status','wall_seconds','peak_rss_kib','swaps']},
 'audited_theorem_roots':roots,'NND_A1_delivered':False,'ledger_rows_closed':0,'status':'target not yet established'}
(E/'NNV_VALIDATION.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({k:result[k] for k in ['scope_count','passes','standard_only_on_all_passing_receipts','combined','NND_A1_delivered']}))
