import NP6_ScalarResult
import NP6_FlatExt
set_option autoImplicit false
noncomputable section
namespace AspisR1.NP6_ResultBridge
open Aeneas Aeneas.Std AspisR1ClaimsUnrolledParent
abbrev Status := core.result.Result Claims r1_wire.Error
abbrev Observation := NP6_ResultUniqueness.Outcome (Fin 4 → Nat) 87

/-- A lossless carrier relation. It records the source Result tag and every
payload component; it is not an equality between two caller outputs. -/
def Represents (r : Status) : Observation → Prop
  | .allocation => r = .Err .Allocation
  | .bad i => ∃ offset : Usize, offset.val = i.val ∧ r = .Err (.NonCanonical 25#u8 offset)
  | .returned values => ∃ out : Claims, r = .Ok out ∧ NP6_FlatExt.fields out = values

theorem injective (r s : Status) (o : Observation)
    (hr : Represents r o) (hs : Represents s o) : r = s := by
  cases o with
  | allocation => exact hr.trans hs.symm
  | bad i =>
    obtain ⟨a,ha,ra⟩ := hr
    obtain ⟨b,hb,rb⟩ := hs
    have same : a=b := UScalar.eq_of_val_eq (ha.trans hb.symm)
    cases same
    exact ra.trans rb.symm
  | returned values =>
    obtain ⟨a,ra,ha⟩ := hr
    obtain ⟨b,rb,hb⟩ := hs
    have same := NP6_FlatExt.injective a b (ha.trans hb.symm)
    cases same
    exact ra.trans rb.symm

/-- Exact full Result composition for the fixed Claims carrier. The concrete
unary gates supply scalar facts; no caller-output equality is a hypothesis. -/
theorem complete_result (reserved : Bool) (input : Fin 87 → Fin 4 → Nat)
    (native reference : Status) (n r : Observation)
    (hn : Represents native n) (hr : Represents reference r)
    (ns : NP6_ScalarResult.Characterizes reserved 2147483647 input n)
    (rs : NP6_ScalarResult.Characterizes reserved 2147483647 input r) :
    native = reference := by
  have same := NP6_ScalarResult.unique reserved 2147483647 input n r ns rs
  cases same
  exact injective native reference n hn hr

#print axioms injective
#print axioms complete_result
end AspisR1.NP6_ResultBridge
end
