import PCD_State
set_option autoImplicit false
namespace PCD
/-- Accepted c-a row. Clause 1 excludes keys by INSTRUCTION METAS, not passed
infos. Clause 2 identifies the callee's final values without constraining them.
No counter, handle, readonly-entry or callee-success field is present. -/
def RuntimeCpiAccountView (keys : Nat → Key) (admitted : Nat → Prop)
    (instruction : Instruction) (passed : List Nat)
    (before after : Nat → CellView) (calleeFinal : Key → CellView) : Prop :=
  (∀ i, admitted i → (∀ m ∈ instruction.metas, m.key ≠ keys i) → after i = before i) ∧
  (∀ i, admitted i → i ∈ passed → (∃ m ∈ instruction.metas, m.key = keys i) →
    after i = calleeFinal (keys i))

theorem omitted_key_frame (keys : Nat → Key) (admitted : Nat → Prop)
    (instruction : Instruction) (passed : List Nat)
    (before after : Nat → CellView) (calleeFinal : Key → CellView)
    (law : RuntimeCpiAccountView keys admitted instruction passed before after calleeFinal)
    (i : Nat) (live : admitted i) (omitted : ∀ m ∈ instruction.metas, m.key ≠ keys i) :
    after i = before i := law.1 i live omitted

theorem passed_key_view (keys : Nat → Key) (admitted : Nat → Prop)
    (instruction : Instruction) (passed : List Nat)
    (before after : Nat → CellView) (calleeFinal : Key → CellView)
    (law : RuntimeCpiAccountView keys admitted instruction passed before after calleeFinal)
    (i : Nat) (live : admitted i) (inInfos : i ∈ passed)
    (inMetas : ∃ m ∈ instruction.metas, m.key = keys i) :
    after i = calleeFinal (keys i) := law.2 i live inInfos inMetas
#print axioms omitted_key_frame
#print axioms passed_key_view
end PCD
