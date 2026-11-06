import NJE_RoundTrace

set_option autoImplicit false
noncomputable section
namespace NJP_ControllerTrace
open Aeneas Aeneas.Std Result
abbrev State := NJE_RoundTrace.State

/-- Ruling (ad) fixed controller descriptor. The tag includes the enum variant,
not just its payload. NJP_K006/K007 certify this schedule with |_| {}. -/
def descriptor (r : Fin 22) : Nat × NJA_Trace.Kind := ⟨r.val,NJA_Trace.kind r.val⟩

/-- Reviewed staged transcriptions: leading/cell/linear clauses are the NJE
cuts, with their CLOSED child replies already substituted at the SAME inputs.
The controller clause is only the K006/K007 descriptor assertion; it asserts no
arithmetic endpoint. The native evidence association is hybrid P6/D188, not a
Lean theorem about Rust execution. -/
structure Cut (input : State) (states : Fin 23 → State)
    (control : Fin 22 → Nat × NJA_Trace.Kind) : Prop where
 controller : ∀ r, control r=descriptor r
 leading : ∃ bs sums args leading,
   states 0=leading 16 ∧ NJE_ExternalStages.Cut input bs sums args leading
 stages : ∀ r, NJE_RoundTrace.Witness (states r.castSucc) (states r.succ) r

/-- Thread the witnessed cuts in the order certified by the native controller.
There is no callee law or successful-child equality hypothesis. -/
theorem result (input : State) (states : Fin 23 → State)
    (control : Fin 22 → Nat × NJA_Trace.Kind) (cut : Cut input states control) :
    NJE_RoundTrace.Canonical (states (Fin.last 22)) ∧
    NJE_RoundTrace.cast (states (Fin.last 22))=R0P.poseidonPermutation (NJE_RoundTrace.cast input) ∧
    (List.ofFn (NJE_RoundTrace.observed input states)).length=22 ∧
    ∀ r, ((NJE_RoundTrace.observed input states r).round,
      (NJE_RoundTrace.observed input states r).kind)=control r := by
 obtain ⟨bs,sums,args,leading,start,initial⟩ := cut.leading
 obtain ⟨canonical,value⟩ := NJE_RoundTrace.composition input states bs sums args leading start initial cut.stages
 refine ⟨canonical,value,by simp,?_⟩
 intro r
 rw [cut.controller r]
 rfl

/-- Event zero retains the original input; every later input is the preceding
output. This matters even though the deployed callback discards the event. -/
theorem chronology (input : State) (states : Fin 23 → State) :
    (NJE_RoundTrace.observed input states 0).input=input ∧
    ∀ r : Fin 21,
      (NJE_RoundTrace.observed input states ⟨r.val+1,by omega⟩).input=
      (NJE_RoundTrace.observed input states ⟨r.val,by omega⟩).output := by
 constructor
 · rfl
 · intro r
   simp only [NJE_RoundTrace.observed]
   simp only [show ¬r.val+1=0 by omega,if_false]
   congr 1

#print result
#print axioms result
#print chronology
#print axioms chronology
end NJP_ControllerTrace
end
