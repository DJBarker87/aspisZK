import NJB_ActiveModel
set_option autoImplicit false
noncomputable section
namespace AspisR1.NJB_ActiveRawHigh
open Aeneas Aeneas.Std Result
open FIv_NativeArithmetic (NQ)
open FIv_NativeValue (Canon decode K)
abbrev State := Fin 7 → NQ
def canonical (s : State) : Prop := ∀ c, Canon (s c)
def decoded (s : State) : Fin 7 → K := fun c => decode (s c)
/-- Reviewed raw reference of the native high-step cut: one read/add/write. -/
def step (high : Fin 64 → NQ) (s : State) (b : Fin 64) : Result State := do
 let c := NJB_ActiveModel.key b
 let out ← FIq_Native.field.QM31.add (s c) (high b)
 pure (fun i => if c=i then out else s i)
theorem step_result (high : Fin 64 → NQ) (s : State) (b : Fin 64)
 (hh : ∀ i,Canon (high i)) (hs : canonical s) :
 ∃ next,step high s b=ok next ∧ canonical next ∧
 decoded next=NJB_ActiveModel.highStep (fun i => decode (high i)) (decoded s) b := by
 obtain ⟨out,call,hout,value⟩ := NJB_StubLaws.qm_add (s (NJB_ActiveModel.key b)) (high b) (hs _) (hh _)
 refine ⟨(fun i => if NJB_ActiveModel.key b=i then out else s i),?_,?_,?_⟩
 · simp only [step,call,bind_tc_ok]
 · intro i
   split <;> first | exact hout | exact hs i
 · funext i
   by_cases same : NJB_ActiveModel.key b=i
   · simp [decoded,NJB_ActiveModel.highStep,same,value,same]
   · simp [decoded,NJB_ActiveModel.highStep,same]
def run (high : Fin 64 → NQ) : List (Fin 64) → State → Result State
 | [],s => ok s
 | b::bs,s => do let next ← step high s b; run high bs next
theorem run_result (high : Fin 64 → NQ) (bs : List (Fin 64)) (s : State)
 (hh : ∀ i,Canon (high i)) (hs : canonical s) :
 ∃ next,run high bs s=ok next ∧ canonical next ∧
 decoded next=NJB_ActiveModel.highRun (fun i=>decode (high i)) bs (decoded s) := by
 induction bs generalizing s with
 | nil => exact ⟨s,rfl,hs,rfl⟩
 | cons b bs ih =>
   obtain ⟨next,call,hnext,value⟩ := step_result high s b hh hs
   obtain ⟨last,lastcall,hlast,lastvalue⟩ := ih next hnext
   refine ⟨last,?_,hlast,?_⟩
   · simp only [run,call,bind_tc_ok,lastcall]
   · simpa only [NJB_ActiveModel.highRun,value] using lastvalue
#print axioms step_result
#print axioms run_result
end AspisR1.NJB_ActiveRawHigh
end
