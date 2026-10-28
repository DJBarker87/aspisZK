from pathlib import Path
import json
E=Path(__file__).resolve().parent
jobs=[('initial_variant_selectors',12,13,'NDE_VariantResults.initial_selectors',14,'all three high QM31 inputs canonical'),('scalar_lanes',14,15,'NDE_ScalarResult.scalar_lanes',15,'output scalar and both branch terms canonical; input asset unrestricted'),('copy_variant',16,17,'NDE_VariantResults.copy_variant',14,'both variants, no word or state restriction')]
p=E/'NDE_LEDGER_DELTA.json';delta=json.loads(p.read_text())
p=E/'NDE_SUPPLEMENTAL.json';spec=json.loads(p.read_text())
for name,positive,negative,theorem,lean,domain in jobs:
 f='crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs::'+name
 row=next(r for r in delta['rows'] if r['function']==f)
 row.clear();row.update(dict(function=f,status='CLOSED',scope='local value bridge; enclosing callers and ABI OPEN',domain=domain,reference='NDE_E003 source snapshot',extraction='NDE_E003',lean=theorem,lean_attempt=lean,positive=positive,negative=negative,copy_fidelity=[8,9],stubs='exact KMX copy_nonoverlapping only; all field additions execute; no stub_verified uses',callee_domain='reference equality is partial-result exact for all words; native contract requires canonical operands to establish no checked overflow; no new core-field bridge claimed'))
 spec.append(dict(id='NDE::'+name,function=f,packet='native-front2-20261028',medium='Kani proof_for_contract plus matched failing control',reference_medium='NCO-pinned extraction plus cohort equality',domain=domain+'; '+theorem+'; local value bridge, enclosing caller-domain/physical association OPEN',positive=[positive],negative=[negative],shape_positive=[8],shape_negative=[9],lean=[lean],reports=['NDE_FRONTIER_BRIDGES.md','NDE_LEDGER_DELTA.json'],additional_receipts=['evidence/native-front2-20261028/NDE_E003/receipt.json'],feature_status='DEPLOYED: exact twelve optimized statement features and isolated deployed graph in native receipts; target/ABI limit retained',admit=True))
(E/'NDE_LEDGER_DELTA.json').write_text(json.dumps(delta,indent=2)+'\n');(E/'NDE_SUPPLEMENTAL.json').write_text(json.dumps(spec,indent=2)+'\n')
p=E/'NDE_FRONTIER_BRIDGES.md';s=p.read_text()
for name,positive,negative,theorem,lean,domain in jobs:
 f='crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs::'+name
 old=next(l for l in s.splitlines() if l.startswith('| `'+f+'`'))
 s=s.replace(old,'| `'+f+'` | CLOSED locally | '+domain+'; '+theorem+f'; E003, L{lean:03}, K{positive:03}/K{negative:03} |')
s+='\nVariant stage: L011 establishes exact extracted-reference addition transport without claiming a native core-field bridge. L012/L013 are excluded initial-selector drafts; L014 and L015 pass with standard axioms. K012/K014/K016 pass, each matched K013/K015/K017 fails exactly one intended ensures check. No contextual substitution is used.\n';p.write_text(s)
