# Shared loop and accumulator progress

FJf_CommonValue.sixteen proves the SAME installed constructor's shared16
multiplication loop values/canonicality and imports FJc_SharedSelf for identity.
FJf_DotPushValue.source derives the actual Q.raw result and the exact four-lane
wrapping update from the actual canonical.Dot.push. Its proof uses the actual
per-coordinate body and induction, with symbolic initial sums, without Kani
stubs or a per-step equality premise. FJf_DotBound.push adds nonwrapping sums
under the actual4096-term cap; FJf_DotFinishValue.value reuses JFv's accepted
finish residue theorem. These are not yet EbyKDot field dot semantics.

FJf_RawReference.source binds all four raw formulas to the actual installed
Q.raw body (stronger than the inherited existential totality theorem).
FJf_RawArithmetic, FJf_RawUV, FJf_Raw23 and FJf_Raw01 now check bounded natural
values, including the source subtractions and partial folds. The field-product
interpretation is the next step. All printed axioms are standard only.

70/100 Lean attempts,0/20 Kani; no timeout/memory kill/cap increase/package replay
or shipped change. FJf_OBSTRUCTION70.md records0/7 complete meanings and the
exact inherited K002 cgroup peak, distinguishing it from this job's direct
kernel-body proofs. Work continues; native/global L142 and top counts remain.
