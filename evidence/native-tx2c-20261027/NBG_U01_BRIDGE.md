# NBG U01 canonical arithmetic and byte carriers — OPEN

This is a staged ledger; the final audit updates pending members. All47 frozen members are classified below. CLOSED means a local helper bridge on the stated domain; it does not prove the enclosing caller establishes that domain.

Frozen4bb3b3f51e16b4525f1d10336e2b0bcbbd775387; source/body hashes NBG_TARGETS.json and NBG_SOURCE_START.json. Cohort is coherent SInt2; newly found CodeField counterpart recorded in NBG_COHORT_CORRECTIONS.md. Native scratch only, no repository crates/programs changes.

| Member | Status | Evidence / domain |
|---|---|---|
| `CM31::add` | CLOSED local | K007; LPi_FieldValues.cm_add; canonical two-limb operands |
| `CM31::double` | CLOSED local | K007; NBG_Additive.cm31_double; canonical operand |
| `CM31::from_le_bytes` | OPEN | See final exact remaining obligations; native-only and model-only stages are not enclosing closure. |
| `CM31::mul` | OPEN | See final exact remaining obligations; native-only and model-only stages are not enclosing closure. |
| `CM31::mul_m31` | OPEN | See final exact remaining obligations; native-only and model-only stages are not enclosing closure. |
| `CM31::new` | CLOSED local | K012; NBG_Constructors.cm31_new; arbitrary raw32 operands |
| `CM31::sub` | CLOSED local | K007; LPi_FieldValues.cm_sub; canonical two-limb operands |
| `CM31::write_le_bytes` | OPEN | See final exact remaining obligations; native-only and model-only stages are not enclosing closure. |
| `M31::add` | CLOSED local | K006; LPi_NatBase.add; operands<P |
| `M31::double` | CLOSED local | K006; NBG_Additive.m31_double; operand<P |
| `M31::from_le_bytes` | CLOSED local | K009; NBG_Atomic.m31_decode; arbitrary four bytes, full Option |
| `M31::inv` | OPEN | See final exact remaining obligations; native-only and model-only stages are not enclosing closure. |
| `M31::mul` | OPEN | See final exact remaining obligations; native-only and model-only stages are not enclosing closure. |
| `M31::reduce_u64` | OPEN | See final exact remaining obligations; native-only and model-only stages are not enclosing closure. |
| `M31::sub` | CLOSED local | K006; LPi_NatBase.sub; operands<P |
| `M31::to_le_bytes` | OPEN | See final exact remaining obligations; native-only and model-only stages are not enclosing closure. |
| `QM31::add` | CLOSED local | K008; LPi_TowerValues.qm_add; canonical four-limb operands |
| `QM31::from_cm31` | CLOSED local | K012; NBG_Constructors.qm31_from_cm31; arbitrary raw32 limbs |
| `QM31::from_le_bytes` | OPEN | See final exact remaining obligations; native-only and model-only stages are not enclosing closure. |
| `QM31::mul` | OPEN | See final exact remaining obligations; native-only and model-only stages are not enclosing closure. |
| `QM31::mul_m31` | OPEN | See final exact remaining obligations; native-only and model-only stages are not enclosing closure. |
| `QM31::square` | OPEN | See final exact remaining obligations; native-only and model-only stages are not enclosing closure. |
| `QM31::sub` | CLOSED local | K008; LPi_TowerValues.qm_sub; canonical four-limb operands |
| `QM31::write_le_bytes` | OPEN | See final exact remaining obligations; native-only and model-only stages are not enclosing closure. |
| `mul_by_r` | CLOSED local | K007; LPi_FieldValues.by_r; canonical two-limb operand |
| `reduce_u64` | OPEN | See final exact remaining obligations; native-only and model-only stages are not enclosing closure. |
| `square_n` | OPEN | See final exact remaining obligations; native-only and model-only stages are not enclosing closure. |
| `WideExact::add` | CLOSED local | K016; NBG_WideCarriers.wide_add; canonical eight-limb operands |
| `WideExact::c0` | OPEN | See final exact remaining obligations; native-only and model-only stages are not enclosing closure. |
| `WideExact::c1` | OPEN | See final exact remaining obligations; native-only and model-only stages are not enclosing closure. |
| `WideExact::from_le_bytes` | OPEN | See final exact remaining obligations; native-only and model-only stages are not enclosing closure. |
| `WideExact::from_limbs` | CLOSED local | K014; NBG_WideCarriers.limbs_result; all raw eight-limb arrays, full Option |
| `WideExact::from_qm31` | OPEN | See final exact remaining obligations; native-only and model-only stages are not enclosing closure. |
| `WideExact::mul` | OPEN | See final exact remaining obligations; native-only and model-only stages are not enclosing closure. |
| `WideExact::mul_m31` | OPEN | See final exact remaining obligations; native-only and model-only stages are not enclosing closure. |
| `WideExact::mul_qm31` | OPEN | See final exact remaining obligations; native-only and model-only stages are not enclosing closure. |
| `WideExact::new` | CLOSED local | K015; NBG_WideCarriers.wide_new; all raw eight limbs, every limb reduced |
| `WideExact::sub` | OPEN | See final exact remaining obligations; native-only and model-only stages are not enclosing closure. |
| `WideExact::to_le_bytes` | OPEN | See final exact remaining obligations; native-only and model-only stages are not enclosing closure. |
| `WideExact::to_limbs` | OPEN | See final exact remaining obligations; native-only and model-only stages are not enclosing closure. |
| `canonical_qm31` | CLOSED local | K015 via both actual WideExact::new calls; NBG_WideCarriers.canonical_qm31; all raw four limbs |
| `mul_u` | OPEN | See final exact remaining obligations; native-only and model-only stages are not enclosing closure. |
| `WideExact::from_m31` | OPEN | See final exact remaining obligations; native-only and model-only stages are not enclosing closure. |
| `Variant::final_len` | CLOSED local | K013; NBG_Transport.final_len_result; all three variants |
| `Variant::folds` | CLOSED local | K013; NBG_Transport.folds_result; all three variants |
| `Variant::tag` | CLOSED local | K013; NBG_Transport.tag_result; all three variants |
| `checkpoint_size` | CLOSED local | K013; NBG_Transport.checkpoint_size_result; all three variants |

## Validation and retained boundaries

Native gates K006–K017 and K027 pass. They establish full coordinate results,
normal rejects and fixed-width writer frames on their stated domains, never
field multiplication or whole source loops. New checked facts are in
NBG_Additive, NBG_Constructors, NBG_Transport, NBG_Atomic, NBG_WideCarriers and
NBG_Embedding; receipts identify exact target,command,revision/source/dependency
hashes,exit,wall,peakRSS,swap and full #print axioms. Accepted prints use only
propext,Classical.choice,Quot.sound or none. Rejected diagnostics are excluded.

The LPi helper dependency closure was missing; nine unchanged modules were
built once into the designated persistent cache. Further optional imports
expose a missing Port5Q1_Ten closure; its focused recovery is in progress.
Original coherent objects and Aeneas library pins remain read-only. No
unchanged timeout/memory-kill replay, cap increase or full manifest occurred.
One admitted high6G/max8G/swap0/tasks64 scope at a time; Lean-M7000.
Every Kani run uses the validated frozen graph, offline optimized compilation,
and matching before/after frozen lock hash. No LPb stage is newly reused.

No headline premise removed. RPx_Deployed.deployed, L154 statement parameter,
narrowed D188,frozen3,RuntimePersistence and game unchanged. SDK/allocator,
compiler/platform/P6, source-to-ELF and actual enclosing call/domain association
remain where not explicitly closed. S2 and deployed100-bit target unestablished.
No shipped/cfg(kani) repository file changed; ELF rebuild trigger did not fire.
Inherited pins, not reproduced: default f8c0ec72621fd5029a97d796c4a3623d0dc44a8e7074122372f9872915d143d4;
devnet63ad3e9cc096dcbb55b3ca7ac7c8e89e6a845796ab5e4f5b7d15db96f3784299;
Pool121f3e29741f510e6dc42d0345fc3c36217600f0be337094855c4a9da2581548.
