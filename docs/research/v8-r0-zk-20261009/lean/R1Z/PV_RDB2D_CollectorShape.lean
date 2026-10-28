import R1Z.PV_RDB2D_PV_B3P_ScheduleResult133
#print Aeneas.Std.core.ptr.alignment.Alignment
namespace R1Z.PV_RDB2D_CollectorShape
open PV_B3P_Schedule133
set_option autoImplicit false

/-- Actual grow_amortized choice after the needs_to_grow branch. -/
def amortized (elementSize cap len additional : Nat) : Nat :=
  max (if elementSize = 1 then 8 else if elementSize ≤ 1024 then 4 else 1)
    (max (cap*2) (len+additional))

/-- The deployed needs_realloc test, restricted to the equal-alignment
non-ZST domain admitted by in_place_collectible. -/
def needsShrink (srcSize dstSize srcCap : Nat) : Bool :=
  if dstSize ≠ 0 ∧ srcSize % dstSize = 0 then false
  else srcCap > 0 && srcCap*srcSize != (srcCap*srcSize/dstSize)*dstSize

theorem filtered_length : (legacyLinks.filter (fun x => !x.path)).length = 64 := by
  rw [PV_B3P_LegacyValues133.legacy_eval]
  rfl

theorem filter_no_shrink (cap : Nat) : needsShrink 8 8 cap = false := by
  simp only [needsShrink,show (8:Nat) ≠ 0 by omega,show (8:Nat)%8=0 by rfl,
    and_self,ite_true]

theorem hypothetical_flat_no_shrink (cap : Nat) : needsShrink 8 2 cap = false := by
  simp only [needsShrink,show (2:Nat) ≠ 0 by omega,show (8:Nat)%2=0 by rfl,
    and_self,ite_true]

/-- FlatMap has SourceIter and TrustedLen but no InPlaceIterable in deployed
core::iter::adapters::flatten. The binding gate selects the TrustedLen
SpecFromIterNested branch; the preceding hypothetical test is not executed. -/
theorem reserve_capacity : amortized 8 127 64 72 = 254 := by rfl

theorem reserve_grows : ¬72 ≤ 127-64 := by omega

theorem reserve_adjusted : 64+190=254 ∧ 64+72=136 := by omega

theorem all_pushes_fit (n : Nat) (h : n ≤ 72) : 64+n ≤ 254 := by omega

theorem flat_length : 136*2=272 := by omega

theorem layouts : 127*8=1016 ∧ 254*8=2032 ∧ 272*2=544 ∧
    1016%2=0 ∧ 2032%2=0 ∧ 544%2=0 := by omega

theorem checked_sizes : (1016:Nat)<2^63 ∧ (2032:Nat)<2^63 ∧ (544:Nat)<2^63 := by
  norm_num

#print axioms filtered_length
#print axioms filter_no_shrink
#print axioms hypothetical_flat_no_shrink
#print axioms reserve_capacity
#print axioms reserve_grows
#print axioms reserve_adjusted
#print axioms all_pushes_fit
#print axioms flat_length
#print axioms layouts
#print axioms checked_sizes
end R1Z.PV_RDB2D_CollectorShape
