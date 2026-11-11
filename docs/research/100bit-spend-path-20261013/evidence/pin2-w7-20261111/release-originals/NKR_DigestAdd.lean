import NKI_LowMixCaller
set_option autoImplicit false
noncomputable section
namespace AspisR1.NKR_DigestAdd
open Aeneas Aeneas.Std Result
open FIv_NativeValue (Canon decode)
open NKI_LowMix (State)
def add (left right : State) : Result State := do
 let a←FIq_Native.field.QM31.add (left 0) (right 0)
 let b←FIq_Native.field.QM31.add (left 1) (right 1)
 ok ![a,b]
/-- Full two-cell addition in native source order, with the canonical domain
proved from each preceding returned state. No multiplication is native. -/
theorem source (left right : State) (hl : ∀ j,Canon (left j)) (hr : ∀ j,Canon (right j)) :
 ∃ out,add left right=ok out ∧ (∀ j,Canon (out j)) ∧
 ∀ j,decode (out j)=decode (left j)+decode (right j) := by
 choose out call ho value using (fun j : Fin 2=>NJB_StubLaws.qm_add (left j) (right j) (hl j) (hr j))
 have vector : (![out 0,out 1] : State)=out := by funext j;fin_cases j <;> rfl
 exact ⟨out,by simp only [add,call,bind_tc_ok,vector],ho,value⟩

def fold : List State → State → Result State
 | [],before=>ok before
 | child::rest,before=>do let middle←add before child;fold rest middle

theorem fold_source (children : List State) (before : State)
 (hc : ∀ child∈children,∀ j,Canon (child j)) (hb : ∀ j,Canon (before j)) :
 ∃ out,fold children before=ok out ∧ (∀ j,Canon (out j)) ∧
 ∀ j,decode (out j)=decode (before j)+(children.map (fun child=>decode (child j))).sum := by
 induction children generalizing before with
 | nil=>exact ⟨before,rfl,hb,by intro j;simp⟩
 | cons child rest ih=>
   obtain ⟨middle,step,hm,vm⟩ := source before child hb (hc child (by simp))
   obtain ⟨out,tail,ho,vo⟩ := ih middle (fun c h=>hc c (by simp only [List.mem_cons];exact Or.inr h)) hm
   refine ⟨out,by simp only [fold,step,bind_tc_ok,tail],ho,?_⟩
   intro j
   rw [vo,vm,List.map_cons,List.sum_cons]
   ring
#print axioms source
#print axioms fold_source
end AspisR1.NKR_DigestAdd
end
