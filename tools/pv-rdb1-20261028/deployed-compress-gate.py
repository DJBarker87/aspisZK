from gate_common import *
F=D.parent/'codex-pv-fscan-20261028';p=F/'src/crates/aspis-r1-cost-probe/src/prover_shared.rs';s=p.read_text()
native=body(s,'fn compress_tagged_tuple(');reference=(D/'compress-owned.rs').read_text();owned=body(reference,'pub fn compress(')
# The only body difference is one local identifier; normalize TOKENS, never
# strings or call names, and require every remaining token to match.
nt=['out' if t=='compressed' else t for t in tok(native)]
assert nt==tok(owned),(native,owned)
expected='{let mut out=QM31::from_cm31(CM31::from_m31(tag));let mut power=lambda;let mut i=0usize;while i<values.len() {out=out.add(power.mul_m31(values[i]));power=power.mul(lambda);i=i.wrapping_add(1);}out}'
assert nt==tok(expected)
checks.append(dict(file=str(p),file_sha256=hashlib.sha256(s.encode()).hexdigest(),complete_body=native,owned_body=owned,owned_sha256=hashlib.sha256(reference.encode()).hexdigest(),body_binding='alpha rename compressed->out only; same types, helper calls/order, constants, bounds and wrapping increment',law='PV_RDB1_V164.complete'))
check('core/src/ptr/non_null.rs','pub const fn cast<U>', '{unsafe {NonNull {pointer:self.as_ptr() as *mut U}}}','Pointer.cast_complete; offset_cast; offset_bounds; no_wrap')
check('core/src/ptr/non_null.rs','pub const fn from_ref(', '{unsafe {NonNull {pointer:r as *const T}}}','PointerConstruct.from_ref_complete; no write or allocation')
check('core/src/ptr/non_null.rs','pub const fn without_provenance(', '{let pointer=crate::ptr::without_provenance(addr.get());unsafe {NonNull {pointer}}}','PointerConstruct.without_provenance_complete; no integer exposure of a live reference')
# All arithmetic calls are shared deployed methods on the same imported core
# types. The original arithmetic/source proofs stand; no Kani multiplication
# chain is introduced, and no fresh arithmetic hypothesis is assumed.
field=F/'src/crates/aspis-core/src/field.rs';ct=F/'src/crates/aspis-core/src/field/ct.rs'
for q in [field,ct]:checks.append(dict(file=str(q),file_sha256=hashlib.sha256(q.read_bytes()).hexdigest(),binding='same deployed QM31/CM31/M31/ct implementations and features for source and owned reference; exact project-all-source-match proof retained'))
j=dict(row='V164',evidence_class='structural (K-1 substitute)',checks=checks,laws=['PV_RDB1_V164.complete','PV_RDB1_V164.index_bounds','PV_RDB1_V164.pointer_read_complete','PV_RDB1_Pointer.cast_complete','PV_RDB1_PointerConstruct.from_ref_complete','PV_RDB1_PointerConstruct.without_provenance_complete'],complete_Result='Both loops bind the same scale,add,mul helpers in the same order, at the same indices. The parametric loop proof preserves every Result variant and divergence; it is not a successful-output-only equation.',effects='Read-only values slice; local accumulator/power/index updated, no allocator/destructor/user callback or input mutation. Existing compiler/binary and side-channel obligations remain.',original_consumption='PV_Op223_Source.op223_p6 and P_source_p6; PV_Op223_V164.refinement retained unchanged including P_proof_bytes/reservation',conservative_edges='Valid index bound excludes panic-formatting envelope; all changed pointer constructors checked explicitly. Intrinsic loads/offsets retain original valid-slice carrier interpretation. No unresolved edge promoted to native helper adequacy.',features=dict(path='resolved-features.json',sha256=hashlib.sha256((D/'resolved-features.json').read_bytes()).hexdigest()),toolchain='1.94.1',profile='release opt3; debug_assertions=false; overflow_checks=false; panic=unwind',native_validation='project-leaves/receipt.json:768 compressor pairs, reused unchanged; finite only',new_trust_items=[],kani_credit=False)
(D/'v164-deployed-binding.json').write_text(json.dumps(j,indent=2)+'\n');print('PASS V164 complete deployed compressor/owned body binding, arbitrary Result loop and pointer laws')
