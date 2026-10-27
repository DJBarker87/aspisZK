import RPu_FJf_CircleBody
import RPu_FJf_CircleIndex
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJf_RawCircleFrame
open Aeneas Aeneas.Std Result ControlFlow
open FJf_PointBody (Factors)
open FJc_WeightQMBridge (SQ)
open FJf_FactorArray (value)

theorem body (k : Usize) (hk : k.val < 2) (j : Nat) (hj : j < 3)
    (iter cursor : FIo_RangeNext.Range) (factors next : Factors) (x x' : SQ)
    (run : FIn_WeightsExtract.weights_new_loop1_loop0.body k iter factors x=
      ok (.cont (cursor,next,x'))) :
    cursor.end=iter.end ∧ cursor.start.val=iter.start.val+1 ∧ iter.start.val < iter.end.val ∧
    next.val[j]?=factors.val[j]? := by
  obtain ⟨di,row,updated,back,digit,hn,hr,hu,hnext⟩ :=
    FJf_CircleBody.cont k iter cursor factors next x x' run
  obtain ⟨readRow,eb⟩ := FJf_ArrayOps.index_mut factors _ row back hr
  have hi := (List.getElem_of_getElem? (FJc_ReadSlot.slot _ _ _ readRow)).choose
  have progress := FIo_RangeNext.some_next iter cursor di hn
  rw [eb] at hnext
  subst next
  refine ⟨progress.2.1,progress.2.2.1,progress.2.2.2,?_⟩
  rw [FJf_ArraySlots.set_slot factors _ updated hi j,if_neg]
  rw [FJf_CircleIndex.value k hk]
  omega

abbrev State := FIo_RangeNext.Range × Factors × SQ

def Inv (base : Factors) (j : Nat) (t : State) : Prop :=
  t.2.1.val[j]?=base.val[j]?

def measure (t : State) : Nat := t.1.end.val-t.1.start.val

theorem step (k : Usize) (hk : k.val < 2) (j : Nat) (hj : j < 3)
    (base : Factors) (t : State) (inv : Inv base j t) (out : ControlFlow State Factors)
    (run : FIn_WeightsExtract.weights_new_loop1_loop0.body k t.1 t.2.1 t.2.2=ok out) :
    match out with
    | .done f => f.val[j]?=base.val[j]?
    | .cont next => Inv base j next ∧ measure next < measure t := by
  rcases t with ⟨iter,factors,x⟩
  cases out with
  | done f =>
    obtain ⟨_,rfl⟩ := FJf_CircleBody.done k iter factors f x run
    exact inv
  | cont next =>
    rcases next with ⟨cursor,f,x'⟩
    obtain ⟨he,hs,hm,hv⟩ := body k hk j hj iter cursor factors f x x' run
    refine ⟨hv.trans inv,?_⟩
    simp only [measure,he,hs];omega

theorem loop (k : Usize) (hk : k.val < 2) (j : Nat) (hj : j < 3)
    (iter : FIo_RangeNext.Range) (factors out : Factors) (x : SQ)
    (run : FIn_WeightsExtract.weights_new_loop1_loop0 iter factors k x=ok out) :
    out.val[j]?=factors.val[j]? := by
  exact FIo_LoopInvariant.preserve
    (fun t : State => FIn_WeightsExtract.weights_new_loop1_loop0.body k t.1 t.2.1 t.2.2)
    (Inv factors j) (fun f => f.val[j]?=factors.val[j]?) measure
    (fun t h r hr => by cases r <;> exact step k hk j hj factors t h _ hr)
    (iter,factors,x) out rfl run
#print axioms body
#print axioms step
#print axioms loop
end AspisR1.FJf_RawCircleFrame
end
