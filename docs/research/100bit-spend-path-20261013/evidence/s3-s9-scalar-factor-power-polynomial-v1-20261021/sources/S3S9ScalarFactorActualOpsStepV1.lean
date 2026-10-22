import S3S9CurrentFieldOpsV1
import S3S9GeneratedWideMulQM31V2

set_option autoImplicit false
open Aeneas Aeneas.Std Result

namespace AspisR1S9ScalarFactorActualOpsStepV1

abbrev Ops := AspisR1S9HelperP6.FieldOps
abbrev S := AspisR1S9HelperP6.field.WideExact
abbrev M := AspisR1S9HelperP6.field.M31
abbrev Q := AspisR1S9HelperP6.field.QM31

@[reducible] def installActualFactorOps (ops : Ops) : Ops :=
  AspisR1S9CurrentFieldOpsV1.installWideAddMulM31
    (AspisR1S9GeneratedWideMulQM31V2.installActualQm31 ops)

theorem installed_wide_mul_qm31_success (ops : Ops) (x : S) (q : Q) (z : S)
    (hx : AspisR1CurrentWide.Proof.CanonicalWide
      (AspisR1S9GeneratedWideMulQM31V2.toWide x))
    (hq : AspisR1CurrentWide.Proof.CanonicalQM
      (AspisR1S9GeneratedWideMulQM31V2.toQM q))
    (h : (letI : Ops := installActualFactorOps ops
      AspisR1S9HelperP6.FieldOps.wideMulQM31 x q) = .ok z) :
    AspisR1CurrentWide.Proof.CanonicalWide
      (AspisR1S9GeneratedWideMulQM31V2.toWide z) ∧
      AspisR1CurrentWide.Proof.decodeWide
        (AspisR1S9GeneratedWideMulQM31V2.toWide z) =
        ⟨AspisR1CurrentWide.Proof.decodeQM
            (AspisR1S9GeneratedWideMulQM31V2.toQM x.c0) *
          AspisR1CurrentWide.Proof.decodeQM
            (AspisR1S9GeneratedWideMulQM31V2.toQM q),
         AspisR1CurrentWide.Proof.decodeQM
            (AspisR1S9GeneratedWideMulQM31V2.toQM x.c1) *
          AspisR1CurrentWide.Proof.decodeQM
            (AspisR1S9GeneratedWideMulQM31V2.toQM q)⟩ := by
  change AspisR1S9GeneratedWideMulQM31V2.actualHelperOperation x q = .ok z at h
  exact AspisR1S9GeneratedWideMulQM31V2.actualHelperOperation_success x q z hx hq h

theorem scalar_factor_call_mut_dispatch (ops : Ops)
    (c : AspisR1S9HelperP6.weights.Weights.scalar_factor.closure)
    (arg : S × Std.Usize) :
    (letI : Ops := installActualFactorOps ops
     AspisR1S9HelperP6.weights.Weights.scalar_factor.closure.Insts.CoreOpsFunctionFnMutPairWideExactUsizeWideExact.call_mut c arg)
    = (letI : Ops := installActualFactorOps ops
       do
      let (a, a1) := c
      let (v, i) := arg
      let permIndex ← Array.index_usize _root_.AspisR1S9HelperP6.weights.PERM i
      let we ← Array.index_usize a permIndex
      let q ← Array.index_usize a1 i
      let we1 ← AspisR1S9GeneratedWideMulQM31V2.actualHelperOperation we q
      let we2 ← AspisR1S9CurrentFieldOpsV1.actualWideAdd v we1
      ok (we2, c)) := by
  rfl

private theorem bind_ok_inv {α β : Type} {r : Result α} {f : α → Result β}
    {x : β} (h : Bind.bind r f = .ok x) :
    ∃ a, r = .ok a ∧ f a = .ok x := by
  cases r with
  | ok a => exact ⟨a,rfl,h⟩
  | fail e => simp [Bind.bind] at h
  | div => simp [Bind.bind] at h

theorem scalar_factor_success_exposes_actual_final_mul
    (ops : Ops) (f : Array Q 4#usize) (p : Array S 4#usize) (out : S)
    (h : (letI : Ops := installActualFactorOps ops
      AspisR1S9HelperP6.weights.Weights.scalar_factor f p) = .ok out) :
    ∃ we,
      (letI : Ops := installActualFactorOps ops
       AspisR1S9HelperP6.FieldOps.iterFold
        (Aeneas.Std.core.iter.traits.iterator.IteratorRange Aeneas.Std.core.iter.range.StepUsize)
        AspisR1S9HelperP6.weights.Weights.scalar_factor.closure.Insts.CoreOpsFunctionFnMutPairWideExactUsizeWideExact
        { start := 0#usize, «end» := 4#usize } AspisR1S9HelperP6.field.WideExact.ZERO (p, f)) = .ok we
      ∧ AspisR1S9CurrentFieldOpsV1.actualWideMulM31 we AspisR1S9HelperP6.weights.QUARTER = .ok out := by
  letI : Ops := installActualFactorOps ops
  change (do
    let we ← AspisR1S9HelperP6.FieldOps.iterFold
      (Aeneas.Std.core.iter.traits.iterator.IteratorRange Aeneas.Std.core.iter.range.StepUsize)
      AspisR1S9HelperP6.weights.Weights.scalar_factor.closure.Insts.CoreOpsFunctionFnMutPairWideExactUsizeWideExact
      { start := 0#usize, «end» := 4#usize } AspisR1S9HelperP6.field.WideExact.ZERO (p, f)
    AspisR1S9CurrentFieldOpsV1.actualWideMulM31 we AspisR1S9HelperP6.weights.QUARTER) = .ok out at h
  exact bind_ok_inv h

#print axioms installed_wide_mul_qm31_success
#print axioms scalar_factor_call_mut_dispatch
#print axioms scalar_factor_success_exposes_actual_final_mul

end AspisR1S9ScalarFactorActualOpsStepV1
