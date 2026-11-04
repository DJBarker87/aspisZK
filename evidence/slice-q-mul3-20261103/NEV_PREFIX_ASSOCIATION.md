# Prefix association review

Frozen function: crates/aspis-r1-cost-probe/src/verifier.rs::batch_prefix_products, revision4bb3b3f51e16b4525f1d10336e2b0bcbbd775387. This is a multiplication-free native append proof joined to the imported emitted arithmetic/loop laws under the explicit P6/D188/Std physical interpretation. It is not a cryptographic assumption removal or a source-to-ELF proof.

## Actual domain and inputs

The frozen function has one source caller, QueryGeometry::for_range at line167. It starts an empty flat Vec and appends exactly five denominators for each successful query in queries[start..end], after guards start<=end<=22. Thus its reached flat cardinalities are5*k with k<=22; the empty branch returns before calling prefix. Every raw denominator word is admitted by the prefix arithmetic law. No nonzero/canonical restriction is added to prefix.

NEV_PrefixCallerDomain.gathered reuses NEB's complete SAME accepted gather induction to expose final flat length5*fuel. capacities proves the finite native family and the110 upper bound. This is model-side caller evidence. The independent native caller gather/borrow/append association is not inferred from this statement and remains an incoming-edge obligation until separately checked. A root-local prefix packet may retain its own stated domain; it does not close QueryGeometry.

## Native prestate and arbitrary window

Each exact_vec<M31,CAP> supplies a valid initialized arbitrary allocation at the actual capacity, then actual truncate sets its live prefix to arbitrary index<CAP. Every live prestate value at that length/capacity has a representative (NEV_PrefixCapacity.representative). Setup is not counted as a verifier loop; the only verifier primitive under test is ONE actual Vec<M31>::push. The native result observes arbitrary offset<=index: old value below index, the input product at index, new length index+1, unchanged pointer and capacity. No field multiplication occurs.

The capacity partitions must cover every positive5*k<=110 before any complete-domain packet is accepted. Capacity110 alone and partial interval coverage have no whole-caller credit. K004/K005 timed-out source shapes stay excluded. Source inputs, source/feature/frozen-lock gates, tool hashes, exact KMX bytes and matched failing controls are retained per attempt. The positive/control configurations differ only in the intended xor-one assertion cfg. No function-pointer dependency, writable static, or contract substitution is used.

The spare-capacity representation is a physical qualification: initialized representatives do not license a read of uninitialized spare bytes. Actual no-growth Vec::push must access only its metadata and write the new cell; this is checked against the pinned native library body during the final review. The arbitrary old-word window is universal, not a uniform/zero-initialized prefix. The vector is a distinct owned allocation from the immutable flat slice. Pointer validity, allocation admission and ABI remain the named physical/P6/library qualifications.

## Same emitted step and arithmetic

Imported NEI_K007/K008 give actual M31 read/product-local-log/checked-index step and its matched corrupted-argument control under the frozen graph/exact KMX/local-record rules. NEV_K028/K029 freshly give initial empty Vec length/capacity for all0..110 under the current strict gate. NEI_K003/K004 are excluded here because the gate changed between them (tool pins and an additional feature check). The imported NEI_K007/K008 domain and original names are preserved; no suspended NEB credit is used.

NEI_PrefixProduct.actual pairs the SAME raw lhs/rhs with both the complete actual frozen emitted M31 body and the adopted prefix callee; it returns ok with exact natural product modulo2147483647 and a canonical reply. No multiplication stub is used in Kani. The existing NEG product abstraction/NEI specialization may choose this reply from the native arbitrary bounded local record. There is no fresh independent operand or product existential.

NEV_PrefixAssembly.windows joins native length, appended-cell and old-word observations at the SAME before/after vector. active passes exactly those observations to NEI_PrefixWindows.source_step. NEI_PrefixStep.total supplies the already-proved finite-loop induction and complete result (prefix list, final product). NEG_PrefixAssociation supplies actual emitted/cohort step and constructor equations. No recurrence or arithmetic theorem is reproved here. There are no digest calls or observable external effects in this function; owned-prefix mutation and the immutable input frame are the state observations to compose.

## Coherent import audit

NEV_L003/L004 are rejected import attempts caused by selecting the later reconciliation public-preparation Types ahead of SInt2's canonical objects. No theorem from either is used. NEV_L005 selects SInt2 before later fallback objects; NEV_L006 first co-imported the prefix/induction chain. NEV_L007 proves the exact M31 call-site and finite-family transport. NEV_L008 is the final joint audit of all thirteen own/imported theorem statements, with every actually resolved Aeneas/AeneasMeta object pinned before execution. All audits use standard axioms. NEV_RESOLVED_LIBRARY_PINS.json records the actual selected Aeneas/AeneasMeta and cohort object hashes read-only; subsequent runner snapshots pin those resolved objects directly.

## Native and inventory review

Every reachable capacity5..110 has a positive/negative pair. NEV_K026/K027 also recheck the exact KMX pointer-copy implementation and failing control in this configuration. The native/library object hashes are recorded in NEV_NATIVE_LIBRARY_PINS.json. The rustc53732d5e0 upstream Vec source is archived as source context, separately qualified from the compiled-library pins. With len<capacity, push_mut skips grow_one, computes ptr+len, writes the input value, increments len and returns the newly written location. No uninitialized spare byte is read. P6/P7 compiler/library correspondence and allocation/reference admission remain explicit qualifications; no Vec::push output specification is assumed.

The original inventory assigned the COMPLETE parent geometry description to prefix rows TX1:185 (geometry) and TX2:111 (U08), including inverse-vector conclusions absent from this function's arguments/result/body. The own ledger corrects only this fragment's input-domain description, retaining the full old text as NEV_original_parent_assignment. The parent QueryGeometry::for_range obligations are unchanged and OPEN. This is a scope correction, not proof of nonzero products, backward inversion or regrouping by a prefix helper. All raw prefix inputs are admitted on the stated length family. Internal fresh allocation/capacity/length is derived from the actual allocation and step certificates, not supplied as a root premise.

NEV_composition.py preserves every original NEI/NEB/NDT gate and adds only an exact-source four-occurrence std-operation class and M31-only receiver resolution. Every added certificate binds the content-addressed review, full Result/value/frame/ordered effects, final kernel audit, native capacity cases and exact imported read/product cut. No older suspended native credit is used.

NEV_L009 additionally packages the complete emitted Result, the returned owned vector values, unchanged modeled external state and empty ordered effects. This is a frame of the model state; the complete physical allocator heap is not asserted unchanged. Its proof is required by the final packet.

## Remaining after local prefix closure

The native capacity, field and finite-loop component can close independently of its parent. The incoming for_range->prefix same-native-call context remains separate from prefix's inner closure. No headline or root status follows from this packet alone.
