import R1Z.PV_CB_CompressCanonicalRead
import R1Z.PV_CB_ForwardRange
import R1Z.ProverRwP6CompressControl
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_CB_CompressCanonicalFinite
open Aeneas Aeneas.Std Result ProverRwFull
variable [ExternalTypes]
abbrev Q := PV_CB_CanonicalTower.Q

theorem finite (ops : ExternalFuns) (values : Slice U32) (lambda : Q)
    (fuel : Nat) (out power : Q) (i : Usize)
    (rank : i.val + fuel = (Slice.len values).val)
    (vv : PV_CB_CompressCanonicalRead.Valid values) (vl : PV_CB_CanonicalTower.Valid lambda)
    (vo : PV_CB_CanonicalTower.Valid out) (vp : PV_CB_CanonicalTower.Valid power) :
    ∃ result, @ProverRwP6CompressControl.finite _ (PV_CB_CompressCanonicalContext.selected ops)
      values lambda fuel out power i = ok result ∧ PV_CB_CanonicalTower.Valid result := by
  induction fuel generalizing out power i with
  | zero =>
    have done : ¬ i < Slice.len values := by change ¬ i.val < (Slice.len values).val; omega
    refine ⟨out,?_,vo⟩
    simp only [ProverRwP6CompressControl.finite,ProverRwP6CompressControl.dispatch,done,if_false]
  | succ fuel ih =>
    have more : i < Slice.len values := by change i.val < (Slice.len values).val; omega
    obtain ⟨m,hm,vm⟩ := PV_CB_CompressCanonicalRead.read values vv i more
    obtain ⟨scaled,hscaled,vscaled⟩ := PV_CB_CanonicalQuarticMore.scale power m
    obtain ⟨nextOut,hout,vout⟩ := PV_CB_CanonicalQuartic.add out scaled vo vscaled
    obtain ⟨nextPower,hpower,vpower⟩ := PV_CB_CanonicalQuartic.mul power lambda vp vl
    have advance : (Usize.wrapping_add i 1#usize).val = i.val+1 :=
      PV_CB_ForwardRange.advance_val i (Slice.len values) more
    obtain ⟨result,hresult,vresult⟩ := ih nextOut nextPower (Usize.wrapping_add i 1#usize)
      (by rw [advance];omega) vout vpower
    refine ⟨result,?_,vresult⟩
    simp only [ProverRwP6CompressControl.finite,ProverRwP6CompressControl.dispatch,more,if_true]
    change (do
      let m ← Slice.index_usize values i
      let q ← PV_CB_CurrentQuartic.S.scale power m
      let nextOut ← PV_CB_CurrentQuartic.S.add out q
      let nextPower ← PV_CB_CurrentQuartic.S.mul power lambda
      @ProverRwP6CompressControl.finite _ (PV_CB_CompressCanonicalContext.selected ops)
        values lambda fuel nextOut nextPower (Usize.wrapping_add i 1#usize)) = ok result
    simp only [hm,hscaled,hout,hpower,hresult,bind_tc_ok]
#print axioms finite
end R1Z.PV_CB_CompressCanonicalFinite
