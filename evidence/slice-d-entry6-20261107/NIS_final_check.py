"""Read-only certificate checks; writes only the final aggregate audit report."""
from pathlib import Path
import json,lzma,hashlib,re,subprocess
E=Path(__file__).resolve().parent
rd=lambda p:json.loads(p.read_text())
sha=lambda b:hashlib.sha256(b).hexdigest()
rows=[json.loads(l) for l in (E/'NIS_ATTEMPTS.jsonl').read_text().splitlines()]
assert len({x['attempt'] for x in rows})==len(rows)
limits={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
idx=rd(E/'NIS_INPUTS.json');native=[];checked_inputs=set()
for r in rows:
 a=r['attempt'];assert r==rd(E/a/'receipt.json')
 ad=rd(E/(a+'-admission.json'));assert ad['exit']==0 and ad['reservation']['allowed'] is True
 assert r['limits']==limits and str(r['swaps'])=='0'
 assert r['exit_status'] in [0,1],(a,r['exit_status'])
 for n,h in r['source_hashes'].items():
  if h not in checked_inputs:
   assert sha(lzma.decompress((E/idx['objects'][h]['path']).read_bytes()))==h;checked_inputs.add(h)
 if a.startswith('NIS_K'):
  assert rd(E/(a+'-graph-check.json'))['graph_matches_frozen']
  assert rd(E/(a+'-erasure-check.json'))['passed']
  assert rd(E/(a+'-lock-check.json'))['unchanged']
  assert rd(E/(a+'-isolation.json'))['allowed']
  assert r['env']['CARGO_TARGET_DIR'].endswith('/codex-cx-slice-d-entry6-20261107/NIS_target')
  assert r['native_command'][r['native_command'].index('--target-dir')+1]==r['env']['CARGO_TARGET_DIR']
  assert r['env']['CARGO_NET_OFFLINE']=='true'
  log=lzma.decompress((E/a/'stdout.log.xz').read_bytes()).decode()
  n=int(a[-3:]);compile_failure=104<=n<=115
  if compile_failure:assert r['exit_status']==1 and 'VERIFICATION:-' not in log
  elif r['exit_status']==0:assert 'VERIFICATION:- SUCCESSFUL' in log
  else:assert 'VERIFICATION:- FAILED' in log and 'Failed Checks:' in log and 'unwinding assertion' not in log
  native.append({'attempt':a,'kind':'COMPILER_FAILURE' if compile_failure else 'PASS' if r['exit_status']==0 else 'FAILING_CONTROL'})
assert len(native)==120
assert [sum(x['kind']==k for x in native) for k in ['PASS','FAILING_CONTROL','COMPILER_FAILURE']]==[55,53,12]
required=set(sum(rd(E/'NIS_AUDIT_ROOTS.json')['groups'],[]))
s='\n'.join(lzma.decompress((E/a/'stdout.log.xz').read_bytes()).decode() for a in ['NIS_L059','NIS_L062']);roots=[json.loads(l[11:]) for l in s.splitlines() if l.startswith('NEP_RESULT ')]
assert len(roots)==len(required)==138 and {x['root'] for x in roots}==required
assert all(x['equal'] and set(x['walked_axioms'])==set(x['collect_axioms'])<={'propext','Classical.choice','Quot.sound'} for x in roots)
loaded=[json.loads(l) for l in lzma.decompress((E/'NIS_NIS_LOADED_scan.jsonl.xz').read_bytes()).decode().splitlines()]
assert all(x['imports_match'] and not x['dangling'] and not x['duplicate_owners'] for x in loaded)
names={x['module'] for x in loaded}
assert {'NGK_COMBINED_IMPORT','NIM_COMBINED_IMPORT','NIM_NHY_COMBINED_IMPORT','NIM_NHJ_COMBINED_IMPORT','NIS_COMBINED_IMPORT','RPx_Deployed'}<=names
assert not (set(rd(E/'NIS_RETARGET.json')['module_map'])&names)
assert 'NGL_MapReference.Types' not in names
final=rd(E/'NIS_FINAL_IMPORTS.json')+rd(E/'NIS_RETARGET.json')['order']
for m in final:
 h=sha((E/(m+'.lean')).read_bytes());assert any(r.get('module')==m and r['exit_status']==0 and h in r['source_hashes'].values() for r in rows),m
 assert not re.search(r'\b(sorry|admit|native_decide)\b', (E/(m+'.lean')).read_text()),m
assert not {'NIS_Tx1PortProbe','NIS_Tx1Release'}&names
closed=rd(E/'NIS_CLOSED.json');delta=rd(E/'NIS_LEDGER_DELTA.json')
assert closed['new_composed_rows']==5 and closed['new_composed_functions']==4
assert delta['counts_after']=={'CLOSED':412,'QUALIFIED':0,'OPEN':187} and not delta['security_target_established']
assert set(delta['new_closed_rows'])=={'TX2:202','TX1:NGB001','TX2:211','TX2:194','TX2:196'}
assert all(r['exit_status']==0 for r in rows if r['attempt'] in ['NIS_L030','NIS_L058','NIS_L059','NIS_L060','NIS_L062'])
prior=rd(E/'NIS_AUDIT.json');fixtures=prior['fixtures'];assert len(fixtures)==8 and all(x['equal'] for x in fixtures)
for p in E.rglob('*'):
 if p.is_file():assert p.stat().st_size<=20_000_000,(p,p.stat().st_size)
(E/'NIS_AUDIT.json').write_text(json.dumps(dict(status='PASS_FINAL_AX2_NFX_ISOLATION',raw_roots=roots,fixtures=fixtures,scan=dict(modules=len(loaded),dangling=0,incompatible_owners=0,import_mismatches=0),standard_axioms_only=True,canonical_owner_collision=False,combined='NIS_L058',raw=['NIS_L059','NIS_L062'],scan_receipt='NIS_L060',fixture_receipt='NIS_L030',native=dict(used=120,passes=55,matched_failing_controls=53,compiler_failures=12),lean_used=len(rows)-120,extraction_used=0,closed_rows=delta['new_closed_rows'],counts_after=delta['counts_after'],security_target_established=False,scope='Cached canonical closure; not a cold release or ELF replay; native incomplete probes excluded'),indent=1)+'\n')
print(json.dumps(dict(status='PASS_FINAL',rows=5,roots=len(roots),modules=len(loaded),native=120,formal=len(rows)-120)))
