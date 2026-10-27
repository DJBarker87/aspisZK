import PV_B3_MaskDictionary134
import PV_B3_MaskSparseBit
namespace PV_B3_Close134
open Aeneas Aeneas.Std Result ProverRwFull PV_B3_MaskDictionary134
set_option autoImplicit false
noncomputable section
-- Exact original dictionary carrier, with its explicit concrete error type.
abbrev Types := R1Z.PV_CBM_MasksSelection.Types
abbrev install := selected

theorem source (base : ExternalTypes) (ops : @ExternalFuns (Types base)) :
    @ExternalFuns.op134 (Types base) (install base ops) =
      ok (.Ok R1Z.PV_Op134_Masks.masks) := op134 base ops

theorem nonvacuity (base : ExternalTypes) (ops : @ExternalFuns (Types base)) :
    ∃ m : Array U16 64#usize,
      @ExternalFuns.op134 (Types base) (install base ops) = ok (.Ok m) ∧ m.val.length = 64 :=
  ⟨_, source base ops, R1Z.PV_Op134_Masks.length⟩

-- Sorting/deduplicating endpoints cannot change their OR mask.
theorem or_idempotent (a : Nat) : a ||| a = a := Nat.or_self a
theorem or_commutative (a b : Nat) : a ||| b = b ||| a := Nat.or_comm a b
theorem or_associative (a b c : Nat) : (a ||| b) ||| c = a ||| (b ||| c) := Nat.or_assoc a b c

#print axioms source
#print axioms nonvacuity
#print axioms or_idempotent
#print axioms or_commutative
#print axioms or_associative
end PV_B3_Close134
