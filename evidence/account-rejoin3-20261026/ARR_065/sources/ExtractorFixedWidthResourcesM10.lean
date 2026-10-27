import RawExtractorCostComposedBin
import ExtractorWorkMonad

/-! Cumulative allocation accounting for a bounded-width event ledger.
The slot count is supplied separately: a bound on work alone is not used
as a proof about allocations. Input storage is not freshly allocated work.
Natural-number bookkeeping may be charged by a size-dependent tariff. -/
set_option autoImplicit false
namespace AspisR1.ExtractorFixedWidthResourcesM10
open RawExtractorCostComposedV2

structure Events where
  field : Nat
  reads : Nat
  control : Nat
  allocated : Nat

def Events.work (e : Events) : Nat := e.field + e.reads + e.control

def Events.add (a b : Events) : Events :=
  ⟨a.field+b.field, a.reads+b.reads, a.control+b.control,
    a.allocated+b.allocated⟩

def Events.resources (e : Events) (width tariff : Nat) : Resources :=
  ⟨e.field, e.reads, e.work*tariff + e.allocated*width⟩

theorem work_add (a b : Events) : (a.add b).work = a.work+b.work := by
  simp only [Events.add, Events.work]
  omega

theorem allocations_add (a b : Events) (ca cb : Nat)
    (ha : a.allocated ≤ ca) (hb : b.allocated ≤ cb) :
    (a.add b).allocated ≤ ca+cb := Nat.add_le_add ha hb

theorem resources_bits_bound (e : Events) (width tariff work slots : Nat)
    (hw : e.work ≤ work) (ha : e.allocated ≤ slots) :
    (e.resources width tariff).bits ≤ work*tariff+slots*width :=
  Nat.add_le_add (Nat.mul_le_mul_right tariff hw) (Nat.mul_le_mul_right width ha)

theorem live_bits (e : Events) (initial live width : Nat)
    (h : live ≤ initial+e.allocated) :
    live*width ≤ (initial+e.allocated)*width :=
  ExtractorWorkMonad.representation_bound live initial e.allocated width h

/-- A common event cap covers both cumulative slots and arithmetic/control
work. It is an explicit premise for the actual annotated schedule. -/
theorem common_cap (e : Events) (B width tariff : Nat)
    (hw : e.work ≤ B) (ha : e.allocated ≤ B) :
    (e.resources width tariff).bits ≤ B*(tariff+width) := by
  have h := resources_bits_bound e width tariff B B hw ha
  simpa only [Nat.mul_add] using h

theorem resources_total_bound (e : Events) (B width tariff : Nat)
    (hw : e.work ≤ B) (ha : e.allocated ≤ B) :
    (e.resources width tariff).total ≤ B*(1+tariff+width) := by
  have hb := common_cap e B width tariff hw ha
  have hf : e.field+e.reads ≤ B := by
    simp only [Events.work] at hw
    omega
  change e.field+e.reads+_ ≤ _
  calc
    _ ≤ B+B*(tariff+width) := Nat.add_le_add hf hb
    _ = _ := by ring

#print axioms work_add
#print axioms allocations_add
#print axioms resources_bits_bound
#print axioms live_bits
#print axioms common_cap
#print axioms resources_total_bound
end AspisR1.ExtractorFixedWidthResourcesM10
