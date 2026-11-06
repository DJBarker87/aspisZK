import NJL_PathStep
set_option autoImplicit false
noncomputable section
namespace AspisR1.NJL_PathTrace
open Aeneas Aeneas.Std Result
open FIv_NativeArithmetic (NQ)
open FIv_NativeValue (Canon decode K)
open NJL_PathContext (Context Domain State)
abbrev Job := Bool × Fin 8
/-- Exact unrolled source order: left0,right0,...,left7,right7. -/
def jobs : List Job := (List.ofFn (fun k : Fin 8=>k)).flatMap (fun k=>[(false,k),(true,k)])
def run (c : Context) (z succ : Fin 16 → NQ) :=
 NJB_StateUpdates.run (fun (job : Job) before=>NJL_PathStep.reference c z succ job.1 job.2 before)
inductive Trace (c : Context) (z succ : Fin 16 → NQ) : List Job → State → State → Prop
 | nil (s) : Trace c z succ [] s s
 | cons {job js before next last} : NJL_PathStep.Step c z succ job.1 job.2 before next →
  Trace c z succ js next last → Trace c z succ (job::js) before last
/-- Every native side cut is instantiated with the SAME actual sub/prepared
Results, in the source's sixteen unrolled call positions. -/
theorem source (c : Context) (z succ : Fin 16 → NQ) (xs : List Job) (before : State)
 (hc : Domain c) (hz : ∀ i,Canon (z i)) (hs : ∀ i,Canon (succ i)) (hb : ∀ i,Canon (before i)) :
 ∃ after,run c z succ xs before=ok after ∧ Trace c z succ xs before after ∧
 (∀ i,Canon (after i)) ∧ (fun i=>decode (after i))=
 xs.foldl (fun before job=>NJL_PathStep.modelStep c z succ job.1 job.2 before) (fun i=>decode (before i)) := by
 induction xs generalizing before with
 | nil => exact ⟨before,rfl,.nil _,hb,rfl⟩
 | cons job js ih =>
  obtain ⟨next,call,cut,hn,value⟩ := NJL_PathStep.source c z succ job.1 job.2 before hc hz hs hb
  obtain ⟨last,rest,trace,hl,vl⟩ := ih next hn
  refine ⟨last,?_,.cons cut trace,hl,?_⟩
  · simp only [run,NJB_StateUpdates.run,call,bind_tc_ok] at rest ⊢
    exact rest
  · simpa only [List.foldl_cons,value] using vl
#print axioms source
end AspisR1.NJL_PathTrace
end
