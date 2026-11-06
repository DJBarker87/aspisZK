from pathlib import Path
import json,lzma,hashlib,subprocess,re
E=Path(__file__).resolve().parent
J=lambda p:json.loads((E/p).read_text())
sha=lambda b:hashlib.sha256(b).hexdigest()
pairs=[(3,4),(5,6)]+[(x,x+1) for x in range(23,44,2)]
checks=[]
for a,b in pairs:
 for n,code in [(a,0),(b,1)]:
  k=f'NJI_K{n:03}';r=J(k+'/receipt.json');assert r['exit_status']==code
  log=lzma.open(E/k/'stdout.log.xz','rt').read()
  assert ('VERIFICATION:- SUCCESSFUL' in log) if code==0 else ('VERIFICATION:- FAILED' in log and 'Failed Checks:' in log and 'unwinding assertion' not in log)
  assert J(k+'-graph-check.json')['graph_matches_frozen']
  assert J(k+'-lock-check.json')['unchanged']
  assert not J(k+'-source-check.json')['errors']
  assert J(k+'-erasure-check.json')['passed']
  assert J(k+'-isolation.json')['allowed']
  adm=J(k+'-admission.json');assert adm['exit']==0 and adm['reservation']['allowed']
  assert r['env']['CARGO_NET_OFFLINE']=='true'
 checks.append(dict(pass_attempt=f'NJI_K{a:03}',matched_failing_control=f'NJI_K{b:03}',verified=True))
for n,code,marker in [(50,1,'assertion failed: weak() == Ok(())'),(51,0,'VERIFICATION:- SUCCESSFUL'),(52,0,'VERIFICATION:- SUCCESSFUL'),(53,1,'Failed Checks: |r| r.is_err()'),(54,1,'is assignable')]:
 k=f'NJI_K{n:03}';r=J(k+'/receipt.json');assert r['exit_status']==code
 log=lzma.open(E/k/'stdout.log.xz','rt').read();assert marker in log
 assert J(k+'-graph-check.json')['graph_matches_frozen'] and J(k+'-lock-check.json')['unchanged']
 assert J(k+'-erasure-check.json')['passed'] and not J(k+'-source-check.json')['errors']
 assert J(k+'-isolation.json')['allowed']
for m in re.findall(r'^import (NJI_[\w.]+)',(E/'NJI_COMBINED_IMPORT.lean').read_text(),re.M)+['NJI_COMBINED_IMPORT']:
 h=sha((E/(m+'.lean')).read_bytes());attempts=[json.loads(l) for l in (E/'NJI_ATTEMPTS.jsonl').read_text().splitlines()]
 assert any(r['module']==m and r['exit_status']==0 and h in r['source_hashes'].values() for r in attempts),m
for r in attempts:
 assert r['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'},r['attempt']
 assert int(r['swaps'])==0
 if r['kind']=='lean':assert '-M7000' in r['command']
patch=Path('evidence/kani-mitig-20261028/KMX_copy_stubs.patch')
assert sha(patch.read_bytes())==J('NJI_KMX_PATCH.json')['sha256']==J('NJI_KMX_FINAL.json')['patch_sha256']
assert J('NJI_AUDIT.json')['status']=='PASS_AX2_NFX_COMBINED'
changed=subprocess.check_output(['git','diff','--name-only','f7a82a4c8df^','HEAD'],text=True).splitlines()
assert all(p.startswith('evidence/tx2-decoders-20261108/') for p in changed)
assert not list(E.rglob('*.rs'))
for p in E.rglob('*'):
 if p.is_file():assert p.stat().st_size<=20_000_000,p
result=dict(status='PASS_LOCAL_CANDIDATES_PENDING_LEDGER',target_established=False,paired_native_checks=checks,contract_shape_controls=dict(shape='Result<(),PoolV1VerifierRegistryFormatError>',weak_proof='NJI_K051',real_body='NJI_K052',unimplied_fails='NJI_K050',inverted_ensures_fails='NJI_K053',modifies_violation_detected='NJI_K054',preflight_failure_no_credit='NJI_K047',reason='Exact enum Arbitrary is scratch-only, covers all12 variants, no renamed harness or weaker assertion'),kmx_patch_sha256=sha(patch.read_bytes()),budget=dict(kani_allocated=54,kani_limit=60,formal_allocated=62,formal_limit=70,extraction_used=1,extraction_limit=1,prelaunch_conservatively_charged=['NJI_K007']),source_change_assessment='Evidence-only NJI changes. No shipped crates/programs/Lean target change. No ELF rebuild trigger; inherited artifact pins only.',elf_pins=dict(default='f8c0ec72621fd5029a97d796c4a3623d0dc44a8e7074122372f9872915d143d4',devnet='63ad3e9cc096dcbb55b3ca7ac7c8e89e6a845796ab5e4f5b7d15db96f3784299',Pool='121f3e29741f510e6dc42d0345fc3c36217600f0be337094855c4a9da2581548'),fresh_elf_build=False,key_operations=False,shared_or_sibling_writes=False,new_trust_rows=[],whole_budget_rationale='NJI_REMAINING.md',full_combined_audits=1)
(E/'NJI_FINAL_CHECK.json').write_text(json.dumps(result,indent=1)+'\n')
print('Final checks passed;54 native/62 formal/1 extraction; four ledger candidates, four OPEN')
