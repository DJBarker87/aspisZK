import LPm_PowersBridge
set_option autoImplicit false
namespace AspisR1.LPm_WeightedField
open Aeneas Aeneas.Std Result LPi_FieldValues

def addE (a b : EW) : EW := (addQ a.1 b.1,addQ a.2 b.2)

theorem add (x y : NE) (hx : canonE x) (hy : canonE y) :
    ∃ out, FIo_Native.aspis_core.field.wide_exact.WideExact.add x y=ok out ∧
      canonE out ∧ ew out=addE (ew x) (ew y) := by
  obtain ⟨lo,left,lc,lv⟩ := LPi_TowerValues.qm_add x.c0 y.c0 hx.1 hy.1
  obtain ⟨hi,right,rc,rv⟩ := LPi_TowerValues.qm_add x.c1 y.c1 hx.2 hy.2
  exact ⟨⟨lo,hi⟩,by simp only [FIo_Native.aspis_core.field.wide_exact.WideExact.add,left,right,bind_tc_ok],
    ⟨lc,rc⟩,Prod.ext lv rv⟩

/-- One exact source multiply/add call sequence, with both values derived
from the emitted operations on their canonical caller domain. -/
theorem step (sum k part : NE) (hs : canonE sum) (hk : canonE k) (hp : canonE part) :
    ∃ out, (do let term ← FIo_Native.aspis_core.field.wide_exact.WideExact.mul k part
               FIo_Native.aspis_core.field.wide_exact.WideExact.add sum term)=ok out ∧
      canonE out ∧ ew out=addE (ew sum) (mulE (ew k) (ew part)) := by
  obtain ⟨term,mult,canonical,value⟩ := LPi_TowerValues.wide_mul k part hk hp
  obtain ⟨out,call,hc,hv⟩ := add sum term hs canonical
  exact ⟨out,by rw [mult,bind_tc_ok,call],hc,by rw [value] at hv; exact hv⟩

def fold (sum : EW) : List (NE×NE) → EW
  | [] => sum
  | (k,p)::xs => fold (addE sum (mulE (ew k) (ew p))) xs

inductive Trace : List (NE×NE) → NE → NE → Prop where
  | done (sum : NE) : Trace [] sum sum
  | step {k p sum next out : NE} {xs : List (NE×NE)}
      (canonicalK : canonE k) (canonicalP : canonE p)
      (call : (do let term ← FIo_Native.aspis_core.field.wide_exact.WideExact.mul k p
                  FIo_Native.aspis_core.field.wide_exact.WideExact.add sum term)=ok next)
      (tail : Trace xs next out) : Trace ((k,p)::xs) sum out

theorem trace_value {xs : List (NE×NE)} {sum out : NE} (tr : Trace xs sum out)
    (hs : canonE sum) : canonE out ∧ ew out=fold (ew sum) xs := by
  induction tr with
  | done sum => exact ⟨hs,rfl⟩
  | @step k p sum next out xs hk hp call tail ih =>
    obtain ⟨actual,actualCall,hc,hv⟩ := step sum k p hs hk hp
    have same : actual=next := Result.ok.inj (actualCall.symm.trans call)
    subst actual
    obtain ⟨last,value⟩ := ih hc
    exact ⟨last,by rw [fold,←hv]; exact value⟩

#print axioms add
#print axioms step
#print axioms trace_value
end AspisR1.LPm_WeightedField
