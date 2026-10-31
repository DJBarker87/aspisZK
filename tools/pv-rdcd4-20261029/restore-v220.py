"""Fail-closed V220 source/Result restoration; never upgrades a pin to checker."""
from pathlib import Path
import json,hashlib,subprocess
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-rdcd4-20261029'
required=['FieldSource','LazyComponents','LazyCell','LazyPair','LazyChannels','LazyAccumulate','LazyReconstruct','LazyProducts','RadixBlock','RadixLoop','LazyShape','V220','RangeAPI194']
receipts={}
for p in sorted(E.glob('lean-*/receipt.json')):
 x=json.load(open(p))
 if x['exit']==0:
  receipts[x['module']]=dict(x,receipt=str(p.relative_to(E)))
missing=['R1Z/PV_RDCD4_'+m for m in required if 'R1Z/PV_RDCD4_'+m not in receipts]
assert not missing,missing
for m in required:
 x=receipts['R1Z/PV_RDCD4_'+m];assert hashlib.sha256((R/x['source_path']).read_bytes()).hexdigest()==x['source_sha256'],m
 assert all('sorryAx' not in a for a in x['axioms']),m
c=json.load(open(E/'v220-coherence/receipt.json'));assert c['exit']==0
coh=json.load(open(E/'v220-coherence-result.json'));assert coh['external_count']==5673
for m in required:assert 'R1Z/PV_RDCD4_'+m in coh['modules'],m
assert len(coh['additional_native_source_pins'])==8
census=json.load(open(E/'v220-source-census.json'));assert len(census['records'])==20 and len(census['field_bindings'])==26
bodies=json.load(open(E/'v220-body-bindings.json'));assert len(bodies['records'])==5 and len(bodies['reference_bindings'])==6
leaves=json.load(open(E/'v220-leaf-bindings.json'));assert len(leaves['records'])==6
root=receipts['R1Z/PV_RDCD4_V220']
association=dict(row='V220',theorem='R1Z.PV_RDCD4_V220.source_reference',before='Complete deployed source-value/Result equality with the loop-free lazy radix-four owned reference was unbound.',after='For every original Array<QM31,28> and QM31 challenge, concrete source and complete loop-free owned reference have identical Result. No new callback or hypothesis.',source_records=['v220-source-census.json','v220-body-bindings.json','v220-leaf-bindings.json'],proof_modules={m:receipts['R1Z/PV_RDCD4_'+m] for m in required},source_scope='ct-host-prover release configuration; original source and full Result carrier. Private list backing storage maps to fixed initialized arrays through Index194/ArrayWrite194, exact nested writeback and LazyShape row/column/update invariants. Index bounds cover all seven radix blocks and word arithmetic. Wrapping arithmetic follows deployed overflow_checks=false.',original_checker='UNRECOVERED; structural k-prime substitute only',b3p6_1_reclassifications=0,evidence_class='structural (K-1 substitute); reclassification within existing Aeneas/Rust/compiler trust',nonclaims=['No Horner/polynomial-meaning law is inferred from control-flow equality.','No deployed-prefix/canonical-reachability, shipped-binary or endpoint world/observer theorem.','Historical128 polynomial pairs remain finite validation and are not rerun.'],retained=['V370/D381/D386','E1/E2','native RunJoin/carrier/world and physical observer','client proof-account route','L1/L2/L3','T exactly entropy_law/entropy_kernel/observation'],endpoint_premises_removed=[],endpoint_premises_added=[],endpoint_premises_changed=[])
(E/'v220-proof-association.json').write_text(json.dumps(association,indent=2)+'\n')
x=json.load(open(E/'rows/V220.json'));x.update(status='RESTORED',rdcd4_status='RESTORED at source-value/Result boundary',**{'class':'B'},source_classification_complete=True,concrete_native_cone_complete_at_stated_primitive_boundary=True,native_link_evidence_class=association['evidence_class'],source_revision=root['source_revision'],coherence_revision=c['source_revision'],known_source_cause_classes=['unchanged selected field bodies','concrete1.94.1 library/loop transport','unrecovered original checker replaced by structural k-prime binding'],reason=association['after'],kernel_theorem=association['theorem'],evidence_class=association['evidence_class'],source_association='v220-proof-association.json',coherence='v220-coherence-result.json',next_deliverable='Final combined audit, focused restored-row replay and single frozen manifest; remaining external/meaning obligations retain their original statements.')
(E/'rows/V220.json').write_text(json.dumps(x,indent=2)+'\n')
(E/'rows/V220.md').write_text(f'''# V220 — RESTORED / B

Evidence class: **structural (K-1 substitute)**, reclassification within existing
Aeneas/Rust/compiler trust. Exact theorem: **`{association['theorem']}`**.
It compares the original concrete radix-four source with the complete loop-free
owned lazy-product reference for every original typed coefficient array and challenge,
retaining the full Result carrier and introducing no callback or hypothesis.

[Source association](../v220-proof-association.json) records26 unchanged field
bodies,8 reused range/index bodies,5 complete lazy/root bodies and6 concrete
wrapping/range wrapper bodies. All20 conservative envelope records are dispositioned.
The complete original checker remains unrecovered; no projection or pin tool is
relabelled as that checker. Zero b3p6-1 reclassifications are credited.

The nested row-major writeback, initialized array shape, public index/word bounds,
three-product loop and descending radix loop have named kernel transports.
Root receipt [{root['attempt']}](../{root['receipt']}): exit0, wall{root['wall']},
peak{root['peak_rss_kib']}KiB, swap{root['swap']}; exact revision and target in receipt.
[Independent coherent closure](../v220-coherence/receipt.json): exit0,
wall{c['wall']}, peak{c['peak_rss_kib']}KiB, swap{c['swap']};
all5673 external hashes, successful private imports and deployed source pins checked.

Before/after: the same source-to-owned-reference Result statement is now bound.
No endpoint premise is removed, added or changed. This control-flow equality
supplies no new Horner/polynomial-meaning, canonical-reachability or native
world/physical-observer theorem. V370/D381/D386, E1/E2, native RunJoin/world,
client route, L1/L2/L3 and the exact three-item T remain.
Final combined audit and replay are pending until66397–66399.
''')
print('V220 RESTORED / B at exact source/Result boundary; no arithmetic-meaning or endpoint claim.')
