from pathlib import Path
import subprocess,json,lzma,hashlib
E=Path(__file__).resolve().parent;raw=subprocess.check_output(['git','show','HEAD:evidence/native-ledger3-20261029/NDT_LEDGER.json']);ndt=json.loads(raw);old={r['row']:r for r in ndt['rows']};nir=json.loads(lzma.decompress((E.parent/'ledger12-20261107/NIR_LEDGER.json.xz').read_bytes()));by={r['row']:r for r in nir['rows']};review=json.loads((E/'NIU_CANDIDATE_REVIEW.json').read_text());out=[]
for c in review['rows']:
 r=by[c['row']];o=old.get(c['row']);x=dict(row=c['row'],NIR_function=r['function'],NIR_obligation_sha256=r['obligation_statement_hash'],NDT_present=o is not None)
 if o:
  assert o['function']==r['function']and o['frozen_body_sha256']==r['frozen_body_sha256']
  checks={k:o[k]==r['obligation'][k]for k in['named_hypotheses','inventory_domain_obligations','caller_domain_obligations']}
  x.update(frozen_body_identical=True,original_clause_comparison=checks,canonical_callees_identical=o['canonical_callees']==r['canonical_callees'],original_composed_status=o['composed_status'],complete_original_clauses={k:o[k]for k in checks},complete_current_clauses={k:r['obligation'][k]for k in checks},candidate_review=c['semantic_review'])
 else:x.update(reason='Post-NDT inventory addition already authoritative in NIR; use its exact complete obligation, no invented original row',candidate_review=c['semantic_review'])
 out.append(x)
(E/'NIU_NDT_COMPARISON.json').write_text(json.dumps(dict(status='PASS_FROZEN_IDENTITY_AND_EXPLICIT_CLAUSES',NDT_pin='NIU_NDT_PIN.json',NDT_sha256=hashlib.sha256(raw).hexdigest(),rows=out),indent=1)+'\n')
print(json.dumps(dict(stage='NDT comparison',rows=len(out),original_rows=sum(r['NDT_present']for r in out),clause_differences=[r['row']for r in out if r['NDT_present']and not all(r['original_clause_comparison'].values())])))
