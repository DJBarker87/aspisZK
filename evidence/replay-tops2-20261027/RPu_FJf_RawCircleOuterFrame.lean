import RPu_FJf_CircleOuterBody
import RPu_FJf_RawCircleFrame
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJf_RawCircleOuterFrame
open Aeneas Aeneas.Std Result ControlFlow
open FJf_PointBody (Factors)
open FJf_CircleOuterBody (Z)
open FJf_FactorArray (value)
abbrev State := FIo_RangeNext.Range × Factors

def Inv (base : Factors) (j : Nat) (t : State) : Prop :=
  t.1.end.val=2 ∧ t.1.start.val≤2 ∧ t.2.val[j]?=base.val[j]?

def measure (t : State) : Nat := t.1.end.val-t.1.start.val

theorem step (z : Z) (j : Nat) (hj : j < 3) (base : Factors) (t : State)
    (inv : Inv base j t) (out : ControlFlow State Factors)
    (run : FIn_WeightsExtract.weights_new_loop1.body z t.1 t.2=ok out) :
    match out with
    | .done f => f.val[j]?=base.val[j]?
    | .cont next => Inv base j next ∧ measure next < measure t := by
  rcases t with ⟨iter,factors⟩
  dsimp only [Inv] at inv
  cases out with
  | done f =>
    obtain ⟨_,rfl⟩ := FJf_CircleOuterBody.done z iter factors f run
    exact inv.2.2
  | cont next =>
    rcases next with ⟨cursor,f⟩
    obtain ⟨k,row,updated,back,digit,x,hn,hr,hu,hf⟩ :=
      FJf_CircleOuterBody.cont z iter cursor factors f run
    have pr := FIo_RangeNext.some_next iter cursor k hn
    have hk : k.val < 2 := by rw [pr.1];omega
    obtain ⟨readRow,eb⟩ := FJf_ArrayOps.index_mut factors _ row back hr
    have fr := FJf_RawCircleFrame.loop k hk j hj _ (back updated) f x hf
    have ne : (Usize.wrapping_add 3#usize k).val≠j := by
      rw [FJf_CircleIndex.value k hk];omega
    have hi := (List.getElem_of_getElem? (FJc_ReadSlot.slot _ _ _ readRow)).choose
    dsimp only [Inv]
    refine ⟨⟨by rw [pr.2.1];exact inv.1,by omega,?_⟩,?_⟩
    · rw [fr,eb,FJf_ArraySlots.set_slot factors _ updated hi j,if_neg ne]
      exact inv.2.2
    · simp only [measure,pr.2.1,pr.2.2.1];have := pr.2.2.2;omega

theorem two (z : Z) (j : Nat) (hj : j < 3) (factors out : Factors)
    (run : FIn_WeightsExtract.weights_new_loop1 {start:=0#usize,«end»:=2#usize}
      z factors=ok out) :
    out.val[j]?=factors.val[j]? := by
  exact FIo_LoopInvariant.preserve
    (fun t : State => FIn_WeightsExtract.weights_new_loop1.body z t.1 t.2)
    (Inv factors j) (fun f => f.val[j]?=factors.val[j]?) measure
    (fun t h r hr => by cases r <;> exact step z j hj factors t h _ hr)
    ({start:=0#usize,«end»:=2#usize},factors) out
    ⟨rfl,by change (0:Nat)≤2;decide,rfl⟩ run
#print axioms step
#print axioms two
end AspisR1.FJf_RawCircleOuterFrame
end
