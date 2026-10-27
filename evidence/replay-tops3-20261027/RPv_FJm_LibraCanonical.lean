import RPv_FJm_LibraDone
import RPv_FJm_LibraBodyCanonical
import RPu_FIo_GroupCanonical
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJm_LibraCanonical
open Aeneas Aeneas.Std Result ControlFlow
open FIo_FieldBridge (NE NQ)
open FJm_LibraStages (Weights State)
def Inv (s : State) : Prop := s.1.end.val=2 ∧ s.1.start.val ≤ 2 ∧ FIo_ArrayCanon.Holds s.2
def measure (s : State) : Nat := s.1.end.val-s.1.start.val

theorem loop (ap0 ap1 : Weights) (extra : Array NQ 2#usize)
    (cp0 : FIo_ArrayCanon.Holds ap0) (cp1 : FIo_ArrayCanon.Holds ap1)
    (ce : ∀ q∈extra.val,FIo_QMValues.Canon q)
    (iter : FIo_RangeNext.Range) (weights out : Weights) (inv : Inv (iter,weights))
    (run : FIo_Native.weights.factored_s2_libra_weights_loop iter ap0 ap1 extra weights=ok out) :
    FIo_ArrayCanon.Holds out := by
  exact FIo_LoopInvariant.preserve
    (fun s : State=>FIo_Native.weights.factored_s2_libra_weights_loop.body ap0 ap1 extra s.1 s.2)
    Inv FIo_ArrayCanon.Holds measure
    (fun s hs result hr=>by
      rcases s with ⟨cursor,parts⟩
      rcases hs with ⟨he,hstart,hc⟩
      change cursor.end.val=2 at he
      change cursor.start.val ≤ 2 at hstart
      cases result with
      | done value=>
        have same := FJm_LibraDone.value ap0 ap1 extra cursor parts value hr
        rw [same]
        exact hc
      | cont next=>
        rcases next with ⟨cursorOut,partsOut⟩
        obtain ⟨heq,hstep,hlt,hco⟩ := FJm_LibraBodyCanonical.value ap0 ap1 extra cursor cursorOut parts partsOut he cp0 cp1 ce hc hr
        constructor
        · change cursorOut.end.val=2 ∧ cursorOut.start.val ≤ 2 ∧ FIo_ArrayCanon.Holds partsOut
          refine ⟨by rw [heq];exact he,?_,hco⟩
          rw [hstep]
          omega
        · dsimp only [measure]
          rw [heq,hstep]
          omega)
    (iter,weights) out inv run

theorem value (ap0 ap1 : Weights) (extra : Array NQ 2#usize) (out : Weights)
    (cp0 : FIo_ArrayCanon.Holds ap0) (cp1 : FIo_ArrayCanon.Holds ap1)
    (ce : ∀ q∈extra.val,FIo_QMValues.Canon q)
    (run : FIo_Native.weights.factored_s2_libra_weights ap0 ap1 extra=ok out) :
    FIo_ArrayCanon.Holds out := by
  unfold FIo_Native.weights.factored_s2_libra_weights at run
  exact loop ap0 ap1 extra cp0 cp1 ce _ _ out
    ⟨rfl,by change (0:Nat)≤2;decide,FIo_GroupCanonical.zeros _⟩ run
#print axioms loop
#print axioms value
end AspisR1.FJm_LibraCanonical
end
