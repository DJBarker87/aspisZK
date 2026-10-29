"""Restore only the complete owned structural parser route, after kernel/cohort gates."""
from pathlib import Path
import json,hashlib
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-rdcd4-20261029'
required=['SliceRange194','TryArray194','Endian194','BytesSource','ParserWindows','V197'];passed={}
for p in E.glob('lean-*/receipt.json'):
 x=json.load(open(p))
 if x['exit']==0:passed[x['module']]=dict(x,receipt=str(p.relative_to(E)))
for name in required:
 m='R1Z/PV_RDCD4_'+name;assert m in passed,m
 x=passed[m];assert hashlib.sha256((R/x['source_path']).read_bytes()).hexdigest()==x['source_sha256']
 assert all('sorryAx' not in a for a in x['axioms'])
root=passed['R1Z/PV_RDCD4_V197'];cohr=json.load(open(E/'v197-coherence/receipt.json'));assert cohr['exit']==0
coh=json.load(open(E/'v197-coherence-result.json'));assert coh['external_count']==5673
for n in required:assert 'R1Z/PV_RDCD4_'+n in coh['modules']
src=json.load(open(E/'v197-source-bindings.json'));assert len(src['application_bindings'])==3 and len(src['library_bindings'])==9
assoc=dict(row='V197',theorem='R1Z.PV_RDCD4_V197.source_reference',frame='R1Z.PV_RDCD4_V197.frame',source='v197-source-bindings.json',coherence='v197-coherence-result.json',route='owned k-prime/own-1 structural reference of exact unchanged Rust; reclassification within existing Rust/Aeneas/compiler trust',before=src['before'],after='Same arbitrary byte-slice input, complete Result<Option<QM31>>, all checked-range failures, canonical scalar None branches and short-circuit order. Second-half length guard occurs only after successful c0; immutable input frame is preserved. No new callback or premise.',extractor='Pinned Aeneas loan-validation rejection is retained as historical evidence. No extractor output, altered Rust source, waiver or Kani proof is used.',endpoint_premises_removed=[],endpoint_premises_added=[],endpoint_premises_changed=[],retained=['V370/D381/D386','E1/E2','native RunJoin/world/physical observer','client route','L1/L2/L3','T exactly entropy_law/entropy_kernel/observation'])
(E/'v197-proof-association.json').write_text(json.dumps(assoc,indent=2)+'\n')
x=json.load(open(E/'rows/V197.json'));x.update(status='RESTORED',rdcd4_status='RESTORED at unchanged parser source/Result boundary',**{'class':'B'},source_classification_complete=True,concrete_native_cone_complete_at_stated_primitive_boundary=True,native_link_evidence_class=assoc['route'],kernel_theorem=assoc['theorem'],source_revision=root['source_revision'],coherence_revision=cohr['source_revision'],reason=assoc['after'],source_association='v197-proof-association.json',next_deliverable='Final combined audit and exact restored-row replay.')
(E/'rows/V197.json').write_text(json.dumps(x,indent=2)+'\n')
(E/'rows/V197.md').write_text(f'''# V197 — RESTORED / B

**Owned structural k-prime/own-1 route**, within existing Rust/Aeneas/compiler
trust. The pinned Aeneas escaping-reference rejection is recorded and unused;
no extractor rerun, modified Rust, loan-validation waiver or Kani credit.

`{assoc['theorem']}` proves the same complete Result law for every original
byte-slice input. It preserves short-input indexing failures, scalar None
branches, first-half short circuit and the late second-half bounds check.
No eager16-byte guard is introduced. `frame` retains the immutable input;
`Endian194.binding` retains all four bytes and exact little-endian word order.
[Source association](../v197-source-bindings.json) records all three application
bodies and nine concrete library bodies, with readonly array4 copying and no
returned borrow.

[Kernel receipt](../{root['receipt']}): exit0, wall{root['wall']},
peak{root['peak_rss_kib']}KiB, swap{root['swap']}; standard axioms only.
[Coherent closure](../v197-coherence/receipt.json): exit0, wall{cohr['wall']},
peak{cohr['peak_rss_kib']}KiB, swap{cohr['swap']}; all5673 external hashes,
private imports, fresh launch snapshots and recorded source pins pass.

Before/after is the same source-to-owned-reference Result statement. Endpoint
premises removed/added/changed: zero. V370/D381/D386, E1/E2, native world/observer,
client route, L1/L2/L3 and T remain. Final audit/replay pending.
''')
print('V197 RESTORED / B through exact owned structural parser route.')
