import NFF_Cell
set_option autoImplicit false
namespace AspisR1.NFF_ProductCall
open Aeneas Aeneas.Std Result
abbrev Oracle := U64 → U64 → U64

def Law (oracle : Oracle) : Prop := ∀ a b,
  a.val<NEG_DotDomain.P → b.val<NEG_DotDomain.P →
  NEG_ProductAbstraction.Product 64 a.val b.val (oracle a b).val

def call (oracle : Oracle) (a b : U64) : Result U64 :=
  if a.val<NEG_DotDomain.P ∧ b.val<NEG_DotDomain.P then ok (oracle a b) else a*b

/-- Canonical product replies, with unchanged checked behavior outside the
native replacement domain. This is a primitive law, never a whole callee reply. -/
theorem replay (oracle : Oracle) (law : Law oracle) (a b : U64) :
    call oracle a b=a*b := by
  unfold call
  split
  next h =>
    have native:=JFr_TX2_DotBounds.mul a b h.1 h.2
    have value:=NEG_MachineProduct.u64_value a b
    have expected:=law a b h.1 h.2
    have same : oracle a b=UScalar.wrapping_mul a b :=
      UScalar.eq_of_val_eq (expected.trans value.symm)
    simpa only [same] using native.symm
  next h => rfl

#print axioms replay
end AspisR1.NFF_ProductCall
