import RPu_FJf_PointDone
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJf_PointFrame
open Aeneas Aeneas.Std Result ControlFlow
open FJf_PointBody (Factors Points)
open FJf_FactorArray (value)

theorem body (points : Points) (k : Usize) (j : Nat) (hne : k.val≠j)
    (iter cursor : FIo_RangeNext.Range) (factors next : Factors)
    (run : FIn_WeightsExtract.weights_new_loop0_loop0.body points k iter factors=
      ok (.cont (cursor,next))) :
    cursor.end=iter.end ∧ cursor.start.val=iter.start.val+1 ∧ iter.start.val < iter.end.val ∧
    ∀ d s,value next j d s=value factors j d s := by
  obtain ⟨di,tau,ia,ib,p,a,b,row,back,updated,f0,f1,f2,f3,
    hn,ht,hia,hib,hp,ha,hb,href,hrow,hupdated,hnext⟩ :=
    FJf_PointBody.source points k iter cursor factors next run
  obtain ⟨readRow,eb⟩ := FJf_ArrayOps.index_mut factors k row back hrow
  have progress := FIo_RangeNext.some_next iter cursor di hn
  rw [eb] at hnext
  subst next
  refine ⟨progress.2.1,progress.2.2.1,progress.2.2.2,?_⟩
  intro d s
  rw [FJf_FactorArray.outer_set factors k row updated readRow j d s,if_neg hne]

abbrev State := FIo_RangeNext.Range × Factors

def Inv (base : Factors) (j : Nat) (t : State) : Prop :=
  ∀ d s,value t.2 j d s=value base j d s

def measure (t : State) : Nat := t.1.end.val-t.1.start.val

theorem step (points : Points) (k : Usize) (j : Nat) (hne : k.val≠j)
    (base : Factors) (t : State) (inv : Inv base j t) (out : ControlFlow State Factors)
    (run : FIn_WeightsExtract.weights_new_loop0_loop0.body points k t.1 t.2=ok out) :
    match out with
    | .done f => ∀ d s,value f j d s=value base j d s
    | .cont next => Inv base j next ∧ measure next < measure t := by
  rcases t with ⟨iter,factors⟩
  cases out with
  | done f =>
    obtain ⟨_,rfl⟩ := FJf_PointDone.done points k iter factors f run
    exact inv
  | cont next =>
    rcases next with ⟨cursor,f⟩
    obtain ⟨he,hs,hm,hv⟩ := body points k j hne iter cursor factors f run
    refine ⟨?_,?_⟩
    · intro d s
      exact (hv d s).trans (inv d s)
    · simp only [measure,he,hs];omega

theorem loop (points : Points) (k : Usize) (j : Nat) (hne : k.val≠j)
    (iter : FIo_RangeNext.Range) (factors out : Factors)
    (run : FIn_WeightsExtract.weights_new_loop0_loop0 iter points factors k=ok out) :
    ∀ d s,value out j d s=value factors j d s := by
  exact FIo_LoopInvariant.preserve
    (fun t : State => FIn_WeightsExtract.weights_new_loop0_loop0.body points k t.1 t.2)
    (Inv factors j) (fun f => ∀ d s,value f j d s=value factors j d s) measure
    (fun t h r hr => by cases r <;> exact step points k j hne factors t h _ hr)
    (iter,factors) out (by intro d s;rfl) run
#print axioms body
#print axioms step
#print axioms loop
end AspisR1.FJf_PointFrame
end
