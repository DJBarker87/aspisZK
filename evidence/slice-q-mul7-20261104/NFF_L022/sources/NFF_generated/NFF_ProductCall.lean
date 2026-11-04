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
    have bound:=NEG_DotDomain.instantiate a.val b.val h.1 h.2
    have cap : NEG_DotDomain.B<UScalar.size .U64 := by decide
    have fits : a.val*b.val≤UScalar.max .U64 := by
      have cap2 : NEG_DotDomain.B≤UScalar.max .U64 := by decide
      omega
    obtain ⟨out,mul,value⟩:=WP.spec_imp_exists (UScalar.mul_spec (x:=a) (y:=b) fits)
    have native:=law a b h.1 h.2
    unfold NEG_ProductAbstraction.Product at native
    have small : a.val*b.val<2^64 := by
      change NEG_DotDomain.B<2^64 at cap
      omega
    rw [Nat.mod_eq_of_lt small] at native
    have same : oracle a b=out := UScalar.eq_of_val_eq (native.trans value.symm)
    simpa only [same] using mul.symm
  next h => rfl

#print axioms replay
end AspisR1.NFF_ProductCall
