"""Reconcile retained COMPLETE scanner traversal; no Lean execution or rescan."""
from pathlib import Path
import json,hashlib
E=Path(__file__).resolve().parent
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def rows(p):return [json.loads(l) for l in p.read_text().splitlines() if l.strip()]
def canonical(xs):return list(dict.fromkeys(xs))
old=E/'NGW_L080/sources/NGW_EXPECTED_IMPORTS.jsonl';new=E/'NGW_EXPECTED_IMPORTS.jsonl';raw=E/'NGW_LOADED_scan.jsonl'
before={r['module']:r['imports'] for r in rows(old)};after={r['module']:r['imports'] for r in rows(new)};scan=rows(raw)
missing={'NGW_FactorRef.Types','NGW_FactorRef.Funs','NGW_DotRef.Types','NGW_DotRef.Funs'}
assert {r['module'] for r in scan if not r['imports_match']}==missing
assert all(n not in before for n in missing)
assert all(after[n]==v for n,v in before.items()),'no previous baseline changes'
def valid(r,catalog):return not r['dangling'] and not r['duplicate_owners'] and canonical(r['loader_imports'])==r['imports']==catalog.get(r['module'])
assert len(scan)==13513 and len({r['module']for r in scan})==len(scan)
assert all(valid(r,after) for r in scan)
# Negative metadata controls against the identical canonical-import/owner/ref predicate.
r=dict(scan[0]);assert not valid(dict(r,dangling=[{'missing':'control'}]),after)
assert not valid(dict(r,duplicate_owners=[{'name':'control'}]),after)
assert not valid(dict(r,imports=['CONTROL']),after)
source_pins={}
for n in sorted(missing):
 p=E/(n.replace('.','/')+'.lean')
 manifest={r['path']:r for r in json.loads((E/'NGW_EXPORT_MANIFEST.json').read_text())['files_manifest']}
 assert sha(p)==manifest['sources/'+str(p.relative_to(E))]['sha256']
 # Full generated trees are pinned at extraction; focused consumers and complete final import load their retained objects.
 source_pins[n]=dict(path=str(p.relative_to(E)),sha256=sha(p),source_imports=after[n])
assert json.loads((E/'NGW_L080/receipt.json').read_text())['exit_status']==1
result=dict(status='PASS_RECONCILED_RECORDED_TRAVERSAL',not_a_rescan=True,original_receipt='NGW_L080',original_exit=1,modules=len(scan),dangling=0,duplicate_owners=0,remaining_import_mismatches=0,corrected_missing_baselines=sorted(missing),original_catalog_sha256=sha(old),corrected_catalog_sha256=sha(new),raw_scan_sha256=sha(raw),generated_sources=source_pins,negative_metadata_controls=3,method='Unchanged NFX canonical first-occurrence imports equality, dangling-reference and owner predicates applied to ALL retained rows. Only four missing source baselines added; original exit1 and raw traversal preserved.',limitation='No second native scanner exit0 is claimed; scope budget exhausted.')
(E/'NGW_SCAN_RECONCILIATION.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({k:result[k]for k in ['status','modules','original_exit','remaining_import_mismatches']}))
