import NMX_R2_CloneNative
set_option autoImplicit false
noncomputable section
namespace NMX_R2_DeferredValue
open Aeneas Aeneas.Std Result AdapterRw NMX_R2_Carrier NMX_R2_CloneNative
/-- Preserve an already borrowed value or scalar; clone only a deferred error.
This is not a generic T::clone law for allocating Ok payloads. -/
def run {A : Type} (aborts : Bool) (failure : Error)
 (input : core.result.Result A solana_program_error.ProgramError) :
 Result (core.result.Result A solana_program_error.ProgramError) :=
 match input with
 | .Ok value => ok (.Ok value)
 | .Err e => do
   let cloned ← clone aborts failure e
   ok (.Err cloned)

theorem member {A : Type} (aborts : Bool) (failure : Error)
 (input : core.result.Result A solana_program_error.ProgramError) (env : RSL.Env) :
 RSL.RS.ofCloned (reply id input) env
  (NMX_R2_ObserveResult.observe id (run aborts failure input)) := by
 cases input with
 | Ok value => rfl
 | Err e =>
   simp only [run,clone]
   cases allocates : (error e).cloneAllocates with
   | false =>
     simp only [RSL.RS.ofCloned,reply,allocates,Bool.and_false,Bool.false_eq_true,if_false,bind_tc_ok]
     rfl
   | true =>
     simp only [RSL.RS.ofCloned,reply,allocates,Bool.and_true,↓reduceIte]
     cases aborts with
     | false =>
       exact Or.inl ⟨.ok (),[],⟨.ret (.error (error e)),[]⟩,
        Or.inl ⟨(),[],⟨.ret (.ok ()),[]⟩,Or.inl rfl,rfl,rfl⟩,rfl,rfl⟩
     | true =>
       exact Or.inr (Or.inl ⟨[],Or.inr (Or.inl ⟨[],Or.inr rfl,rfl⟩),rfl⟩)
#print axioms member
end NMX_R2_DeferredValue
end
