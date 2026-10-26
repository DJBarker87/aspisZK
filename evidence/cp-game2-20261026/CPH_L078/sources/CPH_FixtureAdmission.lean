import CPH_FixtureEntry
set_option autoImplicit false
noncomputable section
namespace AspisR1.CPH_FixtureAdmission
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry S2W_D189Wrappers
open CPH_FixtureData CPH_FixtureEntry

theorem reader_bound (n : Nat) (small : n < 7) : readerCell n < 8 := by
  unfold readerCell
  split_ifs <;> omega

theorem reader_injective (i j : Nat) (hi : i < 7) (hj : j < 7)
    (same : readerCell i = readerCell j) : i = j := by
  unfold readerCell at same
  split_ifs at same <;> omega

theorem admitted1 : S2W_D189Consolidation.RuntimeEntrypointAdmission
    (model (Nat → Record)) e1 e1.heap 3 := by
  apply admitted
  · intro a
    change a ≠ a+100
    omega
  · intro a small
    change a < 8
    omega
  · intro c
    rfl

theorem admitted2 : S2W_D189Consolidation.RuntimeEntrypointAdmission
    (model (Nat → Record)) e2 e2.heap 7 := by
  apply admitted
  · intro a
    change readerCell a ≠ readerCell a+100
    omega
  · intro a small
    exact reader_bound a small
  · intro c
    rfl

#print axioms reader_bound
#print axioms reader_injective
#print axioms admitted1
#print axioms admitted2
end AspisR1.CPH_FixtureAdmission
end
