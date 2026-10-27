import BEf_Bind
import BEg_Simulation
set_option autoImplicit false
noncomputable section
namespace AspisR1.BEl_CodeCongr
open Aeneas Aeneas.Std Result SdkC_Source

def observe {S A : Type} (out : Result A × S × Log) : Option A × S × Log :=
  BEg_Simulation.observation some out

def continue {S A B : Type} (call : Parts → S → Result Digest × S) (k : A → Code B)
    (out : Option A × S × Log) : Option B × S × Log :=
  match out.1 with
  | none => (none,out.2)
  | some a => observe (BEf_Carrier.run call (k a) out.2.1 out.2.2)

def Equivalent {S A : Type} (call : Parts → S → Result Digest × S) (left right : Code A) : Prop :=
  ∀ state before, observe (BEf_Carrier.run call left state before) =
    observe (BEf_Carrier.run call right state before)

theorem bind_run {S A B : Type} (call : Parts → S → Result Digest × S)
    (code : Code A) (k : A → Code B) (state : S) (before : Log) :
    observe (BEf_Carrier.run call (code >>= k) state before) =
      continue call k (observe (BEf_Carrier.run call code state before)) := by
  rw [BEf_Bind.run]
  generalize BEf_Carrier.run call code state before = out
  obtain ⟨result,state,history⟩ := out
  cases result <;> rfl

theorem bind_head {S A B : Type} (call : Parts → S → Result Digest × S)
    (left right : Code A) (k : A → Code B) (same : Equivalent call left right) :
    Equivalent call (left >>= k) (right >>= k) := by
  intro state before
  rw [bind_run,bind_run,same state before]

theorem bind_tail {S A B : Type} (call : Parts → S → Result Digest × S)
    (code : Code A) (left right : A → Code B)
    (same : ∀ a, Equivalent call (left a) (right a)) :
    Equivalent call (code >>= left) (code >>= right) := by
  intro state before
  rw [bind_run,bind_run]
  generalize observe (BEf_Carrier.run call code state before) = out
  obtain ⟨result,state,history⟩ := out
  cases result with
  | none => rfl
  | some a => exact same a state history

#print axioms bind_run
#print axioms bind_head
#print axioms bind_tail
end AspisR1.BEl_CodeCongr
end
