import RPu_FJf_PointOuterFrame
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJf_RawPointFrame
open Aeneas Aeneas.Std Result ControlFlow
open FJf_PointBody (Factors Points)

theorem body (points : Points) (k : Usize) (j : Nat) (hne : k.val≠j)
    (iter cursor : FIo_RangeNext.Range) (factors next : Factors)
    (run : FIn_WeightsExtract.weights_new_loop0_loop0.body points k iter factors=
      ok (.cont (cursor,next))) :
    cursor.end=iter.end ∧ cursor.start.val=iter.start.val+1 ∧ iter.start.val < iter.end.val ∧
    next.val[j]?=factors.val[j]? := by
  obtain ⟨di,tau,ia,ib,p,a,b,row,back,updated,f0,f1,f2,f3,
    hn,ht,hia,hib,hp,ha,hb,href,hrow,hupdated,hnext⟩ :=
    FJf_PointBody.source points k iter cursor factors next run
  obtain ⟨readRow,eb⟩ := FJf_ArrayOps.index_mut factors k row back hrow
  have hi := (List.getElem_of_getElem? (FJc_ReadSlot.slot _ _ _ readRow)).choose
  have pr := FIo_RangeNext.some_next iter cursor di hn
  rw [eb] at hnext
  subst next
  refine ⟨pr.2.1,pr.2.2.1,pr.2.2.2,?_⟩
  rw [FJf_ArraySlots.set_slot factors k updated hi j,if_neg hne]

abbrev State := FIo_RangeNext.Range × Factors

def Inv (base : Factors) (j : Nat) (t : State) : Prop := t.2.val[j]?=base.val[j]?
def measure (t : State) : Nat := t.1.end.val-t.1.start.val

theorem step (points : Points) (k : Usize) (j : Nat) (hne : k.val≠j)
    (base : Factors) (t : State) (inv : Inv base j t) (out : ControlFlow State Factors)
    (run : FIn_WeightsExtract.weights_new_loop0_loop0.body points k t.1 t.2=ok out) :
    match out with
    | .done f => f.val[j]?=base.val[j]?
    | .cont next => Inv base j next ∧ measure next < measure t := by
  rcases t with ⟨iter,factors⟩
  cases out with
  | done f =>
    obtain ⟨_,rfl⟩ := FJf_PointDone.done points k iter factors f run
    exact inv
  | cont next =>
    rcases next with ⟨cursor,f⟩
    obtain ⟨he,hs,hm,hv⟩ := body points k j hne iter cursor factors f run
    refine ⟨hv.trans inv,?_⟩
    simp only [measure,he,hs];omega

theorem loop (points : Points) (k : Usize) (j : Nat) (hne : k.val≠j)
    (iter : FIo_RangeNext.Range) (factors out : Factors)
    (run : FIn_WeightsExtract.weights_new_loop0_loop0 iter points factors k=ok out) :
    out.val[j]?=factors.val[j]? := by
  exact FIo_LoopInvariant.preserve
    (fun t : State => FIn_WeightsExtract.weights_new_loop0_loop0.body points k t.1 t.2)
    (Inv factors j) (fun f => f.val[j]?=factors.val[j]?) measure
    (fun t h r hr => by cases r <;> exact step points k j hne factors t h _ hr)
    (iter,factors) out rfl run
#print axioms body
#print axioms step
#print axioms loop
end AspisR1.FJf_RawPointFrame
end
