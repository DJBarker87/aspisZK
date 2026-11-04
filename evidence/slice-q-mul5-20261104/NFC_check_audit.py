from pathlib import Path
import json,hashlib,lzma,re,difflib
E=Path(__file__).resolve().parent;F=E.parent/'slice-q-mul4-20261104';P=E.parent/'axaudit2-20261102'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert (F/'NFA_WALKER.lean').read_bytes()==(P/'NEP_WALKER.lean').read_bytes()
roots=json.loads((E/'NFC_PROOF_ROOTS.json').read_text());assert len(roots['groups'])==38
original=(E/'NFC_Driver.lean').read_text();expected=''
for i,group in enumerate(roots['groups']):expected+=('if' if i==0 else 'else if')+' mode == "proof'+str(i)+'" then\n      (#[`NFC_FinalAudit], #['+', '.join('`'+n for n in group)+'])\n    '
expected=original.replace('if mode == "fixtures" then',expected+'else if mode == "fixtures" then',1)
assert (E/'NFC_ProofDriver.lean').read_text()==expected
assert (E/'NFC_PROOF_DRIVER.diff').read_text()==''.join(difflib.unified_diff((F/'NFA_Driver.lean').read_text().splitlines(True),expected.splitlines(True),fromfile='NFA_Driver.lean',tofile='NFC_ProofDriver.lean'))

def results(a):
 log=(E/a/'stdout.log').read_text();assert 'NEP_FAILURE' not in log
 return [json.loads(l.split('NEP_RESULT ',1)[1]) for l in log.splitlines() if l.startswith('NEP_RESULT ')]
fixture=results('NFC_L062');initial=results('NFC_L005');assert fixture==initial and len(fixture)==8
for a in ['NFC_L060','NFC_L061','NFC_L062']:assert json.loads((E/a/'receipt.json').read_text())['exit_status']==0
all_results=[];binary_pins=set();attempts=[]
standard={'propext','Classical.choice','Quot.sound'}
previous=json.loads((E/'NFC_AUDIT.json').read_text()).get('standalone_NFC',{})
previous_pins={x['root']:x['reachable_sha256'] for x in previous.get('results',[])}
for i,group in enumerate(roots['groups']):
 a=f'NFC_L{i+63:03}';r=json.loads((E/a/'receipt.json').read_text());assert r['exit_status']==0
 rs=results(a);assert [x['root'] for x in rs]==group
 for item in rs:
  assert item['equal'] and item['walked_axioms']==item['collect_axioms'] and set(item['walked_axioms'])<=standard
  p=E/('NEP_proof'+str(i)+'_'+item['root']+'_REACHABLE.txt')
  raw=p.read_bytes() if p.exists() else lzma.decompress(Path(str(p)+'.xz').read_bytes())
  digest=hashlib.sha256(raw).hexdigest()
  if item['root'] in previous_pins:assert previous_pins[item['root']]==digest
  sidecar=Path(str(p)+'.sha256')
  if sidecar.exists():assert sidecar.read_text().split()[0]==digest
  lines=raw.decode().splitlines();assert len(lines)==item['reachable_constants'] and item['root'] in lines
  all_results.append(dict(attempt=a,reachable_sha256=hashlib.sha256(raw).hexdigest(),**item))
 pin=json.loads((E/a/'NFC_ProofDriver_BINARY_PIN.json').read_text());binary_pins.add(pin['sha256'])
 attempts.append({k:r[k] for k in ['attempt','module','exit_status','wall_seconds','peak_rss_kib','swaps','source_revision','source_hashes','limits']})
assert {x['root'] for x in all_results}==set(roots['roots']) and len(all_results)==70 and len(binary_pins)==1
agg=json.loads((E/'NFC_L059/receipt.json').read_text());assert agg['exit_status']==0 and len(agg['print_axioms'])==70 and all('sorryAx' not in x for x in agg['print_axioms'])
p=E/'NFC_AUDIT.json';audit=json.loads(p.read_text());audit['standalone_NFC']=dict(status='PASS_STANDALONE_NOT_HEADLINE_JOIN',unique_roots=70,groups=38,zero_unresolved_constants=True,standard_axioms_only=True,raw_graphs_equal_collectAxioms=True,driver_fixture_attempt='NFC_L062',fixture_results=fixture,driver_diff='NFC_PROOF_DRIVER.diff',driver_binary_sha256=next(iter(binary_pins)),results=all_results,attempts=attempts,aggregate_attempt='NFC_L059',print_axioms=agg['print_axioms'],headline_join=dict(attempt='NFC_L058',status='FAILED_IMPORT_OWNER_COLLISION',error="FIo_ReduceBounds duplicates AspisR1.FIo_ReduceBounds.fold from RPt_FIo_ReduceBounds"),credit='No new dot CLOSED rows; source/log/domain theorems only; headline join and incoming certificates OPEN')
p.write_text(json.dumps(audit,indent=2)+'\n');print('PASS: 70 raw roots / 38 groups; eight fixtures; standard-only and zero unresolved. Headline join remains failed.')
