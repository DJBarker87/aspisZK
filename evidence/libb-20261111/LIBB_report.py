"""Summarize immutable scope receipts and current-source own audit coverage."""
from pathlib import Path
import json,hashlib,subprocess,lzma
E=Path(__file__).resolve().parent
receipts=[json.loads(p.read_text()) for p in sorted(E.glob('LIBB_L[0-9][0-9][0-9]/receipt.json'))]
accepted={}
for r in receipts:
 p=E/(r['module']+'.lean')
 if r['kind']=='lean' and r['exit_status']==0 and p.exists() and hashlib.sha256(p.read_bytes()).hexdigest() in r['source_hashes'].values():accepted[r['module']]=r
idx=json.loads((E/'LIBB_AUDIT_INDEX.json').read_text());audits={}
for p in sorted((E/'LIBB_audit').glob('proof*/proof*.json')):
 a=json.loads(p.read_text())
 assert a['exit_status']==0
 for r in a['results']:
  assert set(r['walked_axioms'])<= {'propext','Classical.choice','Quot.sound'},r
  assert r['root'] not in audits,('Duplicate audit',r['root'])
  audits[r['root']]=dict(receipt=str(p.relative_to(E)),axioms=r['walked_axioms'])
coverage=[]
for x in idx:
 p=E/(x['module']+'.lean')
 assert hashlib.sha256(p.read_bytes()).hexdigest()==x['source_sha256']
 coverage.append(dict(**x,audit=audits.get(x['root']),status='audited' if x['root']in audits else 'pending'))
failed=[dict(attempt=r['attempt'],kind=r['kind'],target=r['module'],exit=r['exit_status']) for r in receipts if r['exit_status']!=0]
summary=dict(target_established=False,row_credit_claimed=False,report_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),budget=300,scopes_used=len(receipts),scopes_remaining=300-len(receipts),kani_used=0,extractions_used=0,outer_wall_seconds=sum(r['wall_seconds']for r in receipts),peak_rss_kib=max(int(r['peak_rss_kib'])for r in receipts),swaps=sum(int(r['swaps'])for r in receipts),failed_scopes=failed,changed_source_modules=list(accepted),own_roots=len(idx),raw_audits_completed=len(audits),pending_raw_audits=[x['root'] for x in coverage if x['status']=='pending'],scope_fields=[{k:r.get(k) for k in ['attempt','kind','module','exit_status','wall_seconds','peak_rss_kib','swaps','source_revision','source_hashes','print_axioms','limits','command']} for r in receipts],scope_receipt_pattern='LIBB_LNNN/receipt.json',caps=dict(memoryHigh='6G',memoryMax='8G',memorySwapMax=0,tasksMax=64,leanM=7000),no_caps_raised=True,no_timeouts_raised=True,standard_axioms=['propext','Classical.choice','Quot.sound'],shipped_source_changes=False,combined_import=next((r['attempt']for r in receipts if r['module']=='LIBB_COMBINED_IMPORT'and r['exit_status']==0),'pending'),retained_cache='/home/dombarker/project-offloads/codex-cx-libb-20261111')
(E/'LIBB_VALIDATION.json').write_text(json.dumps(summary,indent=1)+'\n')
(E/'LIBB_AUDIT_COVERAGE.json').write_text(json.dumps(coverage,indent=1)+'\n')
cols=['attempt','kind','module','exit_status','wall_seconds','peak_rss_kib','swaps','source_revision']
lines=['\t'.join(cols+['print_axioms','receipt'])]
for r in receipts:
 ax=' ; '.join(r['print_axioms']).replace('\t',' ').replace('\n',' ')
 lines.append('\t'.join(str(r.get(k,''))for k in cols)+'\t'+ax+'\t'+r['attempt']+'/receipt.json')
(E/'LIBB_TRANSCRIPT.tsv').write_text('\n'.join(lines)+'\n')
assert not any(p.stat().st_size>20_000_000 for p in E.rglob('*')if p.is_file())
print(json.dumps({k:summary[k]for k in ['scopes_used','scopes_remaining','own_roots','raw_audits_completed','swaps']}))
