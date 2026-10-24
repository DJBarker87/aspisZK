import S9ConstructorV3StatementCellCanonicalV1
import S9ConstructorV3BilinearCellSemanticsV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow
namespace AspisR1S9ConstructorV3StatementCellSemanticsV1
open AspisR1S9ConstructorV3Loop2InnerCanonicalV1
open AspisR1S9ConstructorV3StatementCellCanonicalV1
open AspisR1S9ConstructorV3QMMulSemanticsV1

/-- Same successful source statement-cell iteration determines the actual
four values written and proves their bilinear meanings. The point reads,
TAU/index operations and exact mutable row update are witnesses from that
same execution, not separate success assumptions. -/
theorem statement_cell_body_success_semantics
    (points : StatementPoints) (k : Usize) (iter iterNext : R)
    (factors factorsOut : Factors) (hpoints : StatementPointsCanonical points)
    (hbody : AspisR1S9ActualWeightsNewBoxNewV3.weights_new_loop0_loop0.body
      points k iter factors = .ok (.cont (iterNext, factorsOut))) :
    ∃ (d tau i1 ia i3 ib : Usize) (point : StatementRow)
      (a b q0 q1 q2 q3 : Q) (old : Row) (back : Row → Factors) (rowOut : Row),
      core.iter.range.IteratorRange.next core.iter.range.StepUsize iter = .ok (some d, iterNext) ∧
      Array.index_usize AspisR1S9ActualWeightsNewBoxNewV3.TAU d = .ok tau ∧
      lift (Std.Usize.wrapping_mul 2#usize tau) = .ok i1 ∧
      lift (Std.Usize.wrapping_sub 9#usize i1) = .ok ia ∧
      Array.index_usize points k = .ok point ∧ Array.index_usize point ia = .ok a ∧
      lift (Std.Usize.wrapping_mul 2#usize tau) = .ok i3 ∧
      lift (Std.Usize.wrapping_sub 8#usize i3) = .ok ib ∧
      Array.index_usize point ib = .ok b ∧
      Array.index_mut_usize factors k = .ok (old, back) ∧
      Array.update old d (Array.make 4#usize [q0,q1,q2,q3] : Cell) = .ok rowOut ∧
      factorsOut = back rowOut ∧
      Can q0 ∧ Can q1 ∧ Can q2 ∧ Can q3 ∧
      decode q0 = (1-decode a)*(1-decode b) ∧
      decode q1 = decode a*(1-decode b) ∧
      decode q2 = (1-decode a)*decode b ∧
      decode q3 = decode a*decode b := by
  unfold AspisR1S9ActualWeightsNewBoxNewV3.weights_new_loop0_loop0.body at hbody
  obtain ⟨next, hnext, hbody⟩ := bind_success_inv
    (core.iter.range.IteratorRange.next core.iter.range.StepUsize iter) _ _ hbody
  rcases next with ⟨opt, iter1⟩
  cases opt with
  | none =>
    change ok (ControlFlow.done factors : ControlFlow (R × Factors) Factors) =
      ok (ControlFlow.cont (iterNext, factorsOut) : ControlFlow (R × Factors) Factors) at hbody
    cases hbody
  | some d =>
    obtain ⟨tau, htau, hbody⟩ := bind_success_inv _ _ _ hbody
    obtain ⟨i1, hi1, hbody⟩ := bind_success_inv _ _ _ hbody
    obtain ⟨i2, hi2, hbody⟩ := bind_success_inv _ _ _ hbody
    obtain ⟨point, hpoint, hbody⟩ := bind_success_inv (Array.index_usize points k) _ _ hbody
    obtain ⟨a, ha, hbody⟩ := bind_success_inv (Array.index_usize point i2) _ _ hbody
    obtain ⟨i3, hi3, hbody⟩ := bind_success_inv _ _ _ hbody
    obtain ⟨i4, hi4, hbody⟩ := bind_success_inv _ _ _ hbody
    obtain ⟨b, hb, hbody⟩ := bind_success_inv (Array.index_usize point i4) _ _ hbody
    obtain ⟨u, hu, hbody⟩ := bind_success_inv
      (AspisR1S9ActualWeightsNewBoxNewV3.field.QM31.sub
        AspisR1S9ActualWeightsNewBoxNewV3.field.QM31.ONE a) _ _ hbody
    obtain ⟨v, hv, hbody⟩ := bind_success_inv
      (AspisR1S9ActualWeightsNewBoxNewV3.field.QM31.sub
        AspisR1S9ActualWeightsNewBoxNewV3.field.QM31.ONE b) _ _ hbody
    obtain ⟨q0, hq0, hbody⟩ := bind_success_inv
      (AspisR1S9ActualWeightsNewBoxNewV3.field.QM31.mul u v) _ _ hbody
    obtain ⟨q1, hq1, hbody⟩ := bind_success_inv
      (AspisR1S9ActualWeightsNewBoxNewV3.field.QM31.mul a v) _ _ hbody
    obtain ⟨q2, hq2, hbody⟩ := bind_success_inv
      (AspisR1S9ActualWeightsNewBoxNewV3.field.QM31.mul u b) _ _ hbody
    obtain ⟨q3, hq3, hbody⟩ := bind_success_inv
      (AspisR1S9ActualWeightsNewBoxNewV3.field.QM31.mul a b) _ _ hbody
    obtain ⟨mutPair, hmut, hbody⟩ := bind_success_inv (Array.index_mut_usize factors k) _ _ hbody
    rcases mutPair with ⟨old, back⟩
    change (do
      let rowOut ← Array.update old d (Array.make 4#usize [q0, q1, q2, q3] : Cell)
      ok (ControlFlow.cont (iter1, back rowOut) : ControlFlow (R × Factors) Factors)) =
        ok (ControlFlow.cont (iterNext, factorsOut) : ControlFlow (R × Factors) Factors) at hbody
    obtain ⟨rowOut, hrow, hbody⟩ := bind_success_inv _ _ _ hbody
    have hstate := ControlFlow.cont.inj (Result.ok.inj hbody)
    have hOut : back rowOut = factorsOut := congrArg Prod.snd hstate
    have hiter : iter1 = iterNext := congrArg Prod.fst hstate
    subst iterNext
    have haCan := hpoints k point hpoint i2 a ha
    have hbCan := hpoints k point hpoint i4 b hb
    obtain ⟨hc0,hc1,hc2,hc3,hd0,hd1,hd2,hd3⟩ :=
      AspisR1S9ConstructorV3BilinearCellSemanticsV1.bilinear_cell_success_exact
        a b u v q0 q1 q2 q3 haCan hbCan hu hv hq0 hq1 hq2 hq3
    exact ⟨d,tau,i1,i2,i3,i4,point,a,b,q0,q1,q2,q3,old,back,rowOut,
      hnext,htau,hi1,hi2,hpoint,ha,hi3,hi4,hb,hmut,hrow,hOut.symm,
      hc0,hc1,hc2,hc3,hd0,hd1,hd2,hd3⟩

#print axioms statement_cell_body_success_semantics
end AspisR1S9ConstructorV3StatementCellSemanticsV1
