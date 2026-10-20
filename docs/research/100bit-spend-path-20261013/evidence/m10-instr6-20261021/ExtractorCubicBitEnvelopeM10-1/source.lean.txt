import ExtractorFixedWidthResourcesM10

/-! A conservative bit lift for an explicitly annotated event/allocation
schedule. Natural-number operands are allowed to grow with log length; fixed
field width alone is not used to claim constant-cost unbounded indices.
Allocation and operand-envelope premises remain explicit in this lemma. -/
set_option autoImplicit false
namespace AspisR1.ExtractorCubicBitEnvelopeM10
open RawExtractorCostComposedV2

structure Schedule where
  events : Nat
  fieldOps : Nat
  reads : Nat
  allocated : Nat
  maxNatural : Nat

def Schedule.resources (s : Schedule) (width : Nat) : Resources :=
  ⟨s.fieldOps,s.reads,s.events*(s.maxNatural+1)^2+s.allocated*width⟩

theorem total_bound (s : Schedule) (width C S : Nat)
    (hC : 1 ≤ C) (hS : 1 ≤ S)
    (hf : s.fieldOps ≤ s.events) (hr : s.reads ≤ s.events)
    (ha : s.allocated ≤ s.events) (he : s.events ≤ C*S)
    (hn : s.maxNatural+1 ≤ C*S) (hw : width ≤ C^2) :
    (s.resources width).total ≤ 4*C^3*S^3 := by
  let U := C*S
  have hu : 1 ≤ U := Nat.mul_le_mul hC hS
  have hcu : C ≤ U := Nat.le_mul_of_pos_right _ hS
  have he' : s.events ≤ U := he
  have hn' : s.maxNatural+1 ≤ U := hn
  have hw' : width ≤ U^2 := hw.trans (Nat.pow_le_pow_left hcu 2)
  have hp := Nat.mul_le_mul he' (Nat.pow_le_pow_left hn' 2)
  have hs := Nat.mul_le_mul (ha.trans he') hw'
  have hc : U*U^2 = U^3 := by ring
  rw [hc] at hp hs
  have hsquare : 1 ≤ U^2 := by simpa only [pow_two] using Nat.mul_le_mul hu hu
  have hucube : U ≤ U^3 := by
    have h := Nat.mul_le_mul_left U hsquare
    simpa only [Nat.mul_one,hc] using h
  have hff := hf.trans he'
  have hrr := hr.trans he'
  change s.fieldOps+s.reads+(s.events*(s.maxNatural+1)^2+s.allocated*width) ≤ _
  have h : s.fieldOps+s.reads+(s.events*(s.maxNatural+1)^2+s.allocated*width) ≤ 4*U^3 := by omega
  simpa only [U,Nat.mul_pow,Nat.mul_assoc] using h

/-- With S=L+1 this is a cubic query/log envelope. This theorem does not
supply a missing per-primitive event, allocation or natural-operand bound. -/
theorem log_bound (s : Schedule) (width C L : Nat) (hC : 1 ≤ C)
    (hf : s.fieldOps ≤ s.events) (hr : s.reads ≤ s.events)
    (ha : s.allocated ≤ s.events) (he : s.events ≤ C*(L+1))
    (hn : s.maxNatural+1 ≤ C*(L+1)) (hw : width ≤ C^2) :
    (s.resources width).total ≤ 4*C^3*(L+1)^3 :=
  total_bound s width C (L+1) hC (by omega) hf hr ha he hn hw

#print axioms total_bound
#print axioms log_bound
end AspisR1.ExtractorCubicBitEnvelopeM10
