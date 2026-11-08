"""Evidence integrity and ledger invariants, without repeating any proof run."""
from pathlib import Path
import json,lzma,hashlib,subprocess,re
E=Path(__file__).resolve().parent;R=E.parent;H=lambda b:hashlib.sha256(b).hexdigest()
def J(p):return json.loads(lzma.open(p).read()if str(p).endswith('.xz')else p.read_text())
sha_pairs=0
for p in E.rglob('*.xz'):
 q=Path(str(p)[:-3]+'.sha256')
 if q.exists():assert H(lzma.decompress(p.read_bytes()))==q.read_text().strip(),str(p);sha_pairs+=1
snapshots=0
for p in E.glob('NNN_L*/receipt.json'):
 rc=J(p)
 for n,h in rc['source_hashes'].items():
  q=p.parent/'sources'/n;assert q.exists()and H(q.read_bytes())==h,str(q);snapshots+=1
for p in E.rglob('*'):
 if p.is_file():assert p.stat().st_size<=20_000_000,str(p)
assert not list(E.rglob('*.olean'))and not list(E.rglob('*.ir'))
for p in E.glob('*.lean'):
 assert not re.search(r'\b(?:sorry|axiom|admit|native_decide)\b',p.read_text()),str(p)
 assert not re.search(r'set_option\s+(?:maxRecDepth|maxHeartbeats)',p.read_text())
old=J(R/'ledger29-20261111/NNM_LEDGER.json.xz');x=J(E/'NNN_LEDGER.json.xz');a={z['row']:z for z in old['rows']};b={z['row']:z for z in x['rows']}
new={'TX2:240','TX1:333','TX2:221','TX1:330','TX2:213'};assert set(a)==set(b)and len(b)==599
assert {n for n in b if a[n]['status']!=b[n]['status']}==new
for n in b:
 assert b[n]['canonical_callees']==a[n]['canonical_callees']
 assert H(json.dumps(b[n]['obligation'],sort_keys=True,separators=(',',':')).encode())==b[n]['obligation_statement_hash'],n
 if n not in new:assert a[n]==b[n]
assert x['counts']=={'CLOSED':599,'QUALIFIED':0,'OPEN':0}and all(z['status']=='CLOSED'for z in b.values())
assert not x['security_target_established']and x['gate']=='PASS'
tr={z['id']:z for z in x['trust_rows']};ot={z['id']:z for z in old['trust_rows']};assert set(tr)==set(ot)
for n in tr:
 for k in ['statement','removal_condition','trust_class','classification']:
  assert tr[n].get(k)==ot[n].get(k),(n,k)
assert tr['ReviewedTranscription-TX2:240']['status']=='USED'
for n in new:
 assert {'S2TrustedSdkBorrow','TrustedStd','RuntimeClockSlotBinding','RuntimeReturnDataClear','ReviewedTranscription-TX2:240','ReviewedTranscription-TX2:217'}<=set(b[n]['consumes_trust'])
 if n!='TX2:240':assert 'ReviewedTranscription-TX1:344'in b[n]['consumes_trust']
assert next(z for z in x['open_findings']if z['id']=='NKB-F1')['status']=='RESOLVED'
tops={z['id']:z for z in x['top_composition_obligations']};assert tops['TOP:G0']['status']=='OPEN'and tops['TOP:G1b']['status']=='OPEN'and tops['TOP:NMF_B']['status']=='OPEN'
assert tops['TGB-1']['status']=='RESOLVED'and tops['TGB-1']['no_row_status_depends_on_it']
assert 'SEPARATE_HEADER_MODEL'in tops['TGB-1b']['status']
entry=x['NNN_headline_inventory'];assert entry['status']=='CARRIED_TO_HEADLINE'and entry['discharged_by']is None
lines=[s for s in(E/'NNN_L005/stdout.log').read_text().splitlines()if'depends on axioms'in s];assert len(lines)==4
for l in lines:assert set(l.split('[',1)[1].rstrip(']').split(', '))<={'propext','Classical.choice','Quot.sound'}
# Source/frozen pins and statement evidence are checked in the finalizer; no repeat Lean/Rust job.
assert J(E/'NNN_FROZEN_SOURCE_CHECK.json')['status']=='PASS'
assert J(E/'NNN_AUDIT.json')['full_composition_pass']
assert not subprocess.check_output(['git','diff','--check'])
changed=subprocess.check_output(['git','diff','--name-only','09ef4e3f4b3846117e0a547d01d60a1b6947cde2','HEAD'],text=True).splitlines()
assert all(p.startswith('evidence/ledger30-20261111/NNN_')for p in changed)
report=dict(status='PASS',compressed_sha_pairs=sha_pairs,source_snapshots=snapshots,receipts=len(list(E.glob('NNN_L*/receipt.json'))),row_count=599,predecessor_rows_unchanged=594,new_closed_rows=sorted(new),edges_removed=[],trust_statements_changed=[],trust_rows_added=[],trust_rows_removed=[],new_top_print_axioms=lines,no_files_over20MB=True,no_build_outputs_committed=True,shipped_changes=False,key_actions=False,security_target_established=False)
(E/'NNN_VALIDATION.json').write_text(json.dumps(report,sort_keys=True,indent=1)+'\n');print(json.dumps(report))
