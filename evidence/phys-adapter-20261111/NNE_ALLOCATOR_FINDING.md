> Superseded for the top instance by C3-BIN ruling (bo). The arbitrary-allocator obstruction below remains valid. NNE_AbortIndicator proves the ACTUAL D189 reserve/cleanup laws for Bool; NNE_RecordSig.a3/a4/a5 install that instance without an allocator hypothesis or new trust row. See NNE_HANDOFF.md, resume under (bo).

# NNE allocator finding (resume amendment)

Target not established. A3/A4 STOPPED, no new trust. Exact interface fields: `RSL.TAS.NNE_A3.accepted1`, `RSL.TAS.NNE_A4.accepted2` in TAS_Interfaces. The headline binder is `allocator : S2W_D189Wrappers.Allocator A`; its two fields are `allocate : A → Nat → Result A` and `cleanup : A → Result A`. It contains no proposition. State1/state2/final1/final2 are arbitrary headline binders, not projected from the RSL observation.

Missing A3 fact, at the actual headline arguments:

```
∃ allocated,
 reserve allocator (admittedSizes e1 3 firstSizes) state1 = ok allocated ∧
 allocator.cleanup allocated = ok final1
```

Missing A4 fact:

```
∃ allocated,
 reserve allocator (admittedSizes e2 7 secondSizes) state2 = ok allocated ∧
 allocator.cleanup allocated = ok final2
```

`NNE_AllocatorNecessary.first/second` prove these facts NECESSARY for the respective accepted1/2 conclusion, without any source/model/SDK premise. `rejecting` inhabits the exact headline Allocator type and always fails cleanup. `rejecting_first/rejecting_second` prove that no native, copy, Entry, data, slot, initial state or chosen output can be accepted with it, even if admittedSizes is empty. This is a binder-level obstruction, not a counterexample to frozen Rust or proof of an actual accepted RSL execution. The RSL rows and A1/A2 do not mention this allocator or its private states; changing this binder does not change their premises. RuntimeEntrypointAdmission is about SDK entry buffers/counters/records, not allocator cleanup. TrustedStd specifies copy. No existing trust row inspected supplies the two private-state equations.

Do not hide these equations in `Out1/Out2`: TAS says those are carrier equalities of the observation, not an extra accepted-allocator hypothesis. Do not infer them from RSL `Spec.alloc`, which (bl)(3) intentionally leaves private allocation state out. Do not choose a different allocator than the headline binder. An owner must reconcile the physical allocator observation with the headline state binders or change the interface explicitly. This worker does neither.

A5 is affected ONLY on stage1 commit observations: CPP_Invocation.first executes the same allocator-aware D189 first; `Hir_Call.firstEffect` commits only on its complete Ok. A3's missing transition cannot be inferred for arbitrary parent `.invoke` calls either. ASQ8 and reject arms have `(store,.rollback)` regardless of the wrapper's reply; they are independent and proceed using G2 alone. There is no native=model premise for ASQ8.
