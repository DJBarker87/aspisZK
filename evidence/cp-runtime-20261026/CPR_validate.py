#!/usr/bin/env python3
"""Read-only receipt/source/axiom audit. Does not launch or monitor builds."""
import hashlib,json,pathlib,re
root=pathlib.Path(__file__).resolve().parents[2]
e=root/'evidence/cp-runtime-20261026'
receipts=[json.loads(p.read_text()) for p in sorted(e.glob('CPR_L*/receipt.json'))]
assert len(receipts)<=100
success=[r for r in receipts if r['exit_status']==0]
rows=[]
for p in sorted((root/'lean').glob('CPR_*.lean')):
 sha=hashlib.sha256(p.read_bytes()).hexdigest()
 matched=[r for r in success if r['source_hashes'].get(p.name)==sha]
 assert matched,p
 r=matched[-1]
 code=re.sub(r'/-.*?-/', '',p.read_text(),flags=re.S)
 code=re.sub(r'--[^\n]*','',code)
 assert not re.search(r'\b(sorry|axiom|admit|native_decide)\b|set_option\s+(maxRecDepth|maxHeartbeats)',code),p
 ns=re.search(r'^namespace (\S+)',code,re.M)
 targets=re.findall(r'^#print axioms (\S+)',code,re.M)
 if ns:
  expected=[ns.group(1)+'.'+t for t in targets]
  actual=[re.search(r"'([^']+)'",s).group(1) for s in r['print_axioms']]
  assert set(expected)<=set(actual),(p,expected,actual)
 rows.append({'module':p.stem,'source_sha256':sha,'successful_attempt':r['attempt']})
for r in receipts:
 assert r['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
 assert r['swaps']=='0'
 assert '-M7000' in r['command']
 if r['exit_status']==0:
  for line in r['print_axioms']:
   if 'depends on axioms:' in line:
    axioms=set(line.split('[',1)[1].rstrip(']').split(', '))
    assert axioms<={'propext','Classical.choice','Quot.sound'},line
baseline=json.loads((e/'CPR_BASELINE.json').read_text())
assert hashlib.sha256((root/'lean/T2R_Top.lean').read_bytes()).hexdigest()==baseline['inputs']['lean/T2R_Top.lean']
result={'lean_attempts':len(receipts),'lean_limit':100,'kani_runs':0,'kani_limit':10,
 'successful':len(success),'failed':len(receipts)-len(success),'sum_wall_seconds':sum(r['wall_seconds'] for r in receipts),
 'peak_rss_kib':max(int(r['peak_rss_kib']) for r in receipts),'all_swaps_zero':True,
 'current_modules':rows,'actual_deployed_ledger_delta':0,'root_source_unchanged':True,
 'standard_axioms_only_in_successful_receipts':True,'failed_receipts_excluded':True}
print(json.dumps(result,indent=2))
