import FJf_RawPointFrame
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJf_RawPointOuterFrame
open Aeneas Aeneas.Std Result ControlFlow
open FJf_PointBody (Factors Points)
abbrev State := FIo_RangeNext.Range × Factors

def Inv (base : Factors) (j : Nat) (t : State) : Prop :=
  j < t.1.start.val ∧ t.2.val[j]?=base.val[j]?
def measure (t : State) : Nat := t.1.end.val-t.1.start.val

theorem step (points : Points) (j : Nat) (base : Factors) (t : State)
    (inv : Inv base j t) (out : ControlFlow State Factors)
    (run : FIn_WeightsExtract.weights_new_loop0.body points t.1 t.2=ok out) :
    match out with
    | .done f => f.val[j]?=base.val[j]?
    | .cont next => Inv base j next ∧ measure next < measure t := by
  rcases t with ⟨iter,factors⟩
  dsimp only [Inv] at inv
  cases out with
  | done f =>
    obtain ⟨_,rfl⟩ := FJf_PointOuterBody.done points iter factors f run
    exact inv.2
  | cont next =>
    rcases next with ⟨cursor,f⟩
    obtain ⟨k,hn,hf⟩ := FJf_PointOuterBody.cont points iter cursor factors f run
    have pr := FIo_RangeNext.some_next iter cursor k hn
    have fr := FJf_RawPointFrame.loop points k j (by rw [pr.1];omega) _ factors f hf
    dsimp only [Inv]
    refine ⟨⟨by omega,fr.trans inv.2⟩,?_⟩
    simp only [measure,pr.2.1,pr.2.2.1];have := pr.2.2.2;omega

theorem loop (points : Points) (j : Nat) (iter : FIo_RangeNext.Range)
    (factors out : Factors) (hj : j < iter.start.val)
    (run : FIn_WeightsExtract.weights_new_loop0 iter points factors=ok out) :
    out.val[j]?=factors.val[j]? := by
  exact FIo_LoopInvariant.preserve
    (fun t : State => FIn_WeightsExtract.weights_new_loop0.body points t.1 t.2)
    (Inv factors j) (fun f => f.val[j]?=factors.val[j]?) measure
    (fun t h r hr => by cases r <;> exact step points j factors t h _ hr)
    (iter,factors) out ⟨hj,rfl⟩ run
#print axioms step
#print axioms loop
end AspisR1.FJf_RawPointOuterFrame
end
