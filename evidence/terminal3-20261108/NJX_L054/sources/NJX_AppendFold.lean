import NJB_StubLaws
set_option autoImplicit false
noncomputable section
namespace AspisR1.NJX_AppendFold
open Aeneas Aeneas.Std Result
open FIv_NativeArithmetic (NQ)
open FIv_NativeValue (Canon decode K)
abbrev State := Fin 4 → NQ
/-- Four actual additions in source order after the SAME level child. -/
def step (before child : State) : Result State := do
 let a←FIq_Native.field.QM31.add (before 0) (child 0)
 let b←FIq_Native.field.QM31.add (before 1) (child 1)
 let c←FIq_Native.field.QM31.add (before 2) (child 2)
 let d←FIq_Native.field.QM31.add (before 3) (child 3)
 ok ![a,b,c,d]
/-- NJL_K059/K060 four-add/full4cell post-state portion. The actual SAME
index/frontier/opened/high argument binding is retained by caller source. -/
def Cut (before child reply after : State) (adds : Nat) : Prop :=
 adds=4 ∧ after=reply ∧
 ∀ j,FIq_Native.field.QM31.add (before j) (child j)=ok (reply j)

theorem step_source (before child : State) (hb : ∀ i,Canon (before i)) (hc : ∀ i,Canon (child i)) :
 ∃ out,step before child=ok out ∧ Cut before child out out 4 ∧
 (∀ i,Canon (out i)) ∧ ∀ i,decode (out i)=decode (before i)+decode (child i) := by
 choose out calls canonical values using (fun j : Fin 4=>NJB_StubLaws.qm_add (before j) (child j) (hb j) (hc j))
 have vector : (![out 0,out 1,out 2,out 3] : State)=out := by funext i;fin_cases i <;> rfl
 exact ⟨out,by simp only [step,calls,bind_tc_ok,vector],⟨rfl,rfl,calls⟩,canonical,values⟩

def run (child : Fin 20 → State) : List (Fin 20) → State → Result State
 | [],before=>ok before
 | level::rest,before=>do
  let next←step before (child level)
  run child rest next

inductive Trace (child : Fin 20 → State) : List (Fin 20) → State → State → Prop
 | nil (s) : Trace child [] s s
 | cons {level rest before middle after} : step before (child level)=ok middle →
   Cut before (child level) middle middle 4 → Trace child rest middle after → Trace child (level::rest) before after

/-- Generic SUPPORT only:234 must supply each actual child state and its
canonicality internally at the future235 root. No child-success root premise. -/
theorem source (child : Fin 20 → State) (hc : ∀ level j,Canon (child level j))
 (levels : List (Fin 20)) (before : State) (hb : ∀ j,Canon (before j)) :
 ∃ out,run child levels before=ok out ∧ Trace child levels before out ∧
 (∀ j,Canon (out j)) ∧ ∀ j,decode (out j)=decode (before j)+(levels.map (fun level=>decode (child level j))).sum := by
 induction levels generalizing before with
 | nil=>exact ⟨before,rfl,.nil before,hb,by intro j;simp⟩
 | cons level levels ih=>
  obtain ⟨middle,cm,cut,hm,vm⟩ := step_source before (child level) hb (hc level)
  obtain ⟨out,co,tr,ho,vo⟩ := ih middle hm
  refine ⟨out,by simp only [run,cm,bind_tc_ok,co],.cons cm cut tr,ho,?_⟩
  intro j
  rw [vo,vm,List.map_cons,List.sum_cons]
  ring

/-- The required ZERO-initialized20level induction, all4cells, without
unrolling field arithmetic. Still SUPPORT until concrete234 is discharged. -/
theorem zero_source (child : Fin 20 → State) (hc : ∀ level j,Canon (child level j)) :
 ∃ out,run child (List.finRange 20) (fun _=>FIq_Native.field.QM31.ZERO)=ok out ∧
 Trace child (List.finRange 20) (fun _=>FIq_Native.field.QM31.ZERO) out ∧
 (∀ j,Canon (out j)) ∧ ∀ j,decode (out j)=((List.finRange 20).map (fun level=>decode (child level j))).sum := by
 obtain ⟨out,co,tr,ho,vo⟩ := source child hc (List.finRange 20) (fun _=>FIq_Native.field.QM31.ZERO) (fun _=>FIv_NativeValue.zero.1)
 exact ⟨out,co,tr,ho,fun j=>by simpa only [FIv_NativeValue.zero.2,zero_add] using vo j⟩
#print zero_source
#print axioms step_source
#print axioms source
#print axioms zero_source
end AspisR1.NJX_AppendFold
end
