from NLW_audit import *
import sys
for a,target in zip(sys.argv[1::2],sys.argv[2::2]):
 r=audit(a,'audit',target)
 if r['exit_status']:
  # C3-BIN ax2 addendum: raw standard axioms are authoritative.
  # Preserve exit1 and the discrepancy; never re-run or alter the walker.
  assert target.startswith('batch') and r['exit_status']==1,(a,'unexpected exit')
  i=int(target[5:]);manifest=json.loads((E/'NLW_AUDIT_ROOTS.json').read_text())['groups'][i]
  result=json.loads((E/'NLW_audit'/target/('proof'+str(i)+'.json')).read_text())
  assert {x['root'] for x in result['results']}==set(manifest),(a,'missing root')
  assert all(set(x['walked_axioms'])<={'propext','Classical.choice','Quot.sound'} for x in result['results']),(a,'nonstandard raw axiom')
  assert any(not x['equal'] for x in result['results']),(a,'unexplained exit1')
  raw=lzma.decompress((E/a/'stdout.log.xz').read_bytes()).decode()
  assert 'raw graph disagrees with collectAxioms' in raw and 'error:' not in raw.lower(),(a,'unexplained diagnostic')
  print(json.dumps(dict(attempt=a,exit_status_preserved=1,raw_standard_only=True,collector_disagreement_recorded=True)),flush=True)
