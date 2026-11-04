from pathlib import Path
import json,hashlib
E=Path(__file__).resolve().parent
std={'propext','Classical.choice','Quot.sound'}
entries=json.loads((E/'NFA_AUDIT_ROOTS.json').read_text())[:55]
expected={r for e in entries for r in e['roots']};passed={};attempts=[]
for p in sorted(E.glob('NFA_L*/receipt.json')):
 rc=json.loads(p.read_text())
 if rc['kind'] not in ['audit','auditbin'] or rc['exit_status']!=0:continue
 a=rc['attempt'];ad=json.loads((E/(a+'-admission.json')).read_text())
 assert ad['exit']==0 and ad['reservation']['allowed'] is True
 log=(p.parent/'stdout.log').read_text();assert 'NEP_FAILURE' not in log
 rows=[];prints=[]
 for line in log.splitlines():
  if 'depends on axioms:' in line or 'does not depend on any axioms' in line:prints.append(line)
  if line.startswith('NEP_RESULT '):
   x=json.loads(line[11:]);assert x['equal'] is True and x['collect_axioms']==x['walked_axioms']
   assert set(x['walked_axioms'])<=std
   assert x['reachable_constants']>0 and x['edges_scanned']>0
   passed[x['root']]=dict(attempt=a,**x);rows.append(x['root'])
 entry=rc['deps_fingerprint']['audit_entry'];assert set(rows)==set(entry['roots'])
 assert len(prints)==len(rows)
 attempts.append(dict(attempt=a,module=entry['module'],roots=rows,exit_status=rc['exit_status'],wall_seconds=rc['wall_seconds'],peak_rss_kib=rc['peak_rss_kib'],swaps=rc['swaps'],source_revision=rc['source_revision'],source_hashes=rc['source_hashes'],print_axioms=prints,binary_pin=json.loads((p.parent/'NFA_BINARY_PIN.json').read_text()) if (p.parent/'NFA_BINARY_PIN.json').exists() else None))
assert expected<=set(passed), sorted(expected-set(passed))
assert (E/'NFA_WALKER.lean').read_bytes()==(E.parent/'axaudit2-20261102/NEP_WALKER.lean').read_bytes()
assert (E/'NFA_NEP_Driver.lean.txt').read_bytes()==(E.parent/'axaudit2-20261102/NEP_Driver.lean').read_bytes()
out=dict(status='CANDIDATE_COMPLETE_DRIVER_ROOT_ADAPTER_NOT_YET_ADMITTED',walker_unchanged=True,driver_byte_identical=False,driver_changes=['NFA walker module name','NEV root selection','compiled runtime startup, explicit 7000 MiB threshold and LEAN_PATH initialization'],module_groups=len(entries),root_occurrences=sum(len(x['roots']) for x in entries),unique_roots=len(expected),zero_unresolved_constants=True,standard_axioms_only=True,rows_credited=[],rows_pending_admission=['TX1:185','TX2:111','TX1:182','TX2:108'],attempts=attempts,results=[passed[k] for k in sorted(expected)],security_target_established=False)
(E/'NFA_AUDIT.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({k:out[k] for k in ['status','module_groups','root_occurrences','unique_roots','zero_unresolved_constants','standard_axioms_only']}))
