# NHI excluded/failing attempts

- NHE L077 (predecessor): default recursion depth on whole closure rfl. Replaced by isolated NHI_ScalarStep.cell_bind and emitted, L003 exit0. No depth increase.
- NHI L001: isolated bind simplification left reducible tuple lets; L002 tried dsimp but made no progress; L003 added final shallow rfl and passes. No success premise.
- NHI L006: spacing in a ≤ inequality parsed as another token, plus wrapping numeral not reduced. Corrected exact inequality and explicit Nat wrapping-add goal; L007 passes.
- NHI L008/L009: absent CM31.ZERO constant then opaque canonE prevented Decidable synthesis. Exact canonical-predicate reduction added; L010 passes. No axiom or metric change.
- NHI K009: tool input compile error E0277: frozen QM31 has no kani::Arbitrary implementation. No verification reached; no native credit. Fixed owned input construction to q(kani::any::<[u32;4]>()) per array cell, preserving the identical arbitrary-word domain. New attempt uses corrected source under the original g04 name; never an unchanged rerun or a rename to change a verdict.

- NHI L030/L032: importing original module names selected incompatible owners; L031/L034 remove original direct imports and use the canonical inherited NHI/NHE forest only. No owner declaration was copied into an existing module.
- L033 and L060: own preflight detected missing failed prerequisite objects before any formal process. No submission, receipt or formal-budget charge; corrected prerequisite first. NHI_PREFLIGHT_FAILURES.json records both.
- NHI L036/L037: allocator projection simplification and a no-progress dsimp; L038 explicitly reduces Allocation.reserve and proves both outcomes. L042 clone reference used a pure scalar function instead of the lifted Clone instance; L043 corrects the reference and matches the exact array-clone body.
- L047: unresolved implicit array witnesses in producer statement; L049 supplies exact arrays, not an added premise.
- L048/L050: tuple-projection and rank goal normalization in outer induction; L052 explicitly associates body/rank on the same cursor. No cap/depth/time change.
- L051: underconstrained implicit array in group bound proof; L053 supplies exact frozen group table.
- L059: inequality token 0<input parsed as an initial-segment token; L061 spaces the inequality.
- L065: Usize/Nat list-index normalization; L066 gives exact getter carrier equality. L067's word indices needed literal-value normalization; L068 supplies it.
- L069: exact reverse model depends on noncomputable field-value choice; L070 marks the model noncomputable, without changing its statement or axioms.
- L072: concrete width-wrapping equalities were not definitional; L073 proves 1*4=4,4*4=16,16*4=64 under the existing scalar-size bound.
- L074: exact Array getter and in-bounds rewrites missing; L075 proves them from the existing bounds. L076: multiplication-by-one normalization and let-associated update matching; L077 isolates these exact equalities.
- L078: literal Usize64 value equality under simplifier transparency; L079 rewrites the vector length and closes the exact equality.
- L081/L082: S2 dispatch requires exact wrapping 64*32 and exact Slice.len carrier, then deterministic Bool/if reduction; L083 proves these rather than dropping the fallback.

No failure above is claimed to be a real source/model mismatch. All are own proof/input elaboration failures; the exact logs remain. No timed-out or memory-killed formal shape occurred. The optional unpaired K120 gets no native closure credit. Root pair/finish closure is still blocked by OPEN leaf/caller packets, not bridged by success premises.

- L089: own model definition placed letI inside the do grammar incorrectly; L090 moves it outside do, preserving the exact allocation/tensor statement. It passes with standard axioms. L092 first invocation rejected the non-prefixed target before launch; corrected argument NHI_final under the unchanged strict guard, then final audit passes.
