import T2Nat_ReadCongr
import Port5Q2_ReaderSemantic
set_option autoImplicit false
noncomputable section
namespace AspisR1.T2Nat_SemanticJoin
open Aeneas Aeneas.Std Result AspisR1Stage2
open T2Nat_ResultEq

/-- The symbolic withK congruence is applied ten times; emitted branch
normalization is reused rather than kernel-reducing the nested source body. -/
theorem congr (left right : CheckpointBytes4Sections.ReadK)
    (same : ∀ r, EqOk (left r) (right r)) (bytes : Slice U8) (at1 : Usize) :
    EqOk (CheckpointBytes4Ops.semanticUsing left bytes at1)
      (CheckpointBytes4Ops.semanticUsing right bytes at1) := by
  unfold CheckpointBytes4Ops.semanticUsing
  apply T2Nat_ReadCongr.withK left right same
  intro x0 r0
  apply T2Nat_ReadCongr.withK left right same
  intro x1 r1
  apply T2Nat_ReadCongr.withK left right same
  intro x2 r2
  apply T2Nat_ReadCongr.withK left right same
  intro x3 r3
  apply T2Nat_ReadCongr.withK left right same
  intro x4 r4
  apply T2Nat_ReadCongr.withK left right same
  intro x5 r5
  apply T2Nat_ReadCongr.withK left right same
  intro x6 r6
  apply T2Nat_ReadCongr.withK left right same
  intro x7 r7
  apply T2Nat_ReadCongr.withK left right same
  intro x8 r8
  apply T2Nat_ReadCongr.withK left right same
  intro x9 r9
  exact T2Nat_ResultEq.refl _

theorem reference (unwrap : T2Nat_RawJoin.Unwrap)
    (unwrap_ok : ∀ N b, unwrap N (.Ok b)=ok b) (bytes : Slice U8) (start : Usize) :
    EqOk (Port5Q2_ReaderSemantic.semantic (T2Nat_ScalarJoin.readK unwrap) bytes start)
      (CheckpointBytes4Ops.readSemanticAlpha bytes start) := by
  rw [Port5Q2_ReaderSemantic.normalization]
  exact congr _ _ (T2Nat_ScalarJoin.k_eq unwrap unwrap_ok) bytes start

#print axioms congr
#print axioms reference
end AspisR1.T2Nat_SemanticJoin
end
