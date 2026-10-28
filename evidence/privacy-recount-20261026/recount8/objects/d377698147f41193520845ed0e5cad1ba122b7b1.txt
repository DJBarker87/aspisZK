import R1Z.PV_Src_PortFullRoundCopy
import R1Z.BuilderStdCollect
/-! Proof draft reused read-only from srcid d597d31545. This new module is checked independently; no upstream draft is assumed compiled. -/

/-! Finite symbolic round recurrence. Every trace callback remains an explicit
Result computation, including callback errors and returned callback state. -/
set_option autoImplicit false
namespace R1Z.PV_RunJoin_SourceRoundFold
open Aeneas Aeneas.Std Result R0Z.WriterRefine R0Z.PoseidonRefine
open BuilderForestAdmissionPort PV_Src_PortSboxStep

abbrev Output (F : Type) := State × F × U8 × State

def fullSteps {F : Type}
    (callback : core.ops.function.FnMut F poseidon2.Poseidon2RoundTransition Unit)
    (kind : Usize → poseidon2.Poseidon2RoundKind)
    (xs : List (Usize × State)) (s : State) (trace : F) (round : U8) (input : State) :
    Result (Output F) :=
  match xs with
  | [] => ok (s,trace,round,input)
  | (index,c)::tail => do
    let out ← R0PoseidonCopy.full_round s c
    let (_,trace1) ← callback.call_mut trace
      ({round,kind := kind index,input,output := out} : poseidon2.Poseidon2RoundTransition)
    fullSteps callback kind tail out trace1 (U8.wrapping_add round 1#u8) out

theorem full_total (s c : State) : ∃ out,
    R0PoseidonCopy.full_round s c = ok out ∧ Canonical out := by
  letI : Fact (Nat.Prime 2147483647) := ⟨R0Z.m31_prime⟩
  obtain ⟨out,ho,_⟩ := full_round_lift (K := ZMod 2147483647) s c
  refine ⟨out,ho,?_⟩
  rw [R0PoseidonCopy.full_round] at ho
  obtain ⟨x,hx,he⟩ := bind_ok_inv ho
  exact fun j => external_canon x out he j.val j.isLt

#print axioms full_total
end R1Z.PV_RunJoin_SourceRoundFold
