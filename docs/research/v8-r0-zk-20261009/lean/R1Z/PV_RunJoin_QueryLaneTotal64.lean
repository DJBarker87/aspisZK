import R1Z.PV_RunJoin_QueryWordTotal64
import R1Z.PV_RunJoin_QueryHead63
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_QueryLaneTotal64
attribute [local irreducible] PV_RunJoin_WeightInstalled46.selected PV_B2_F_RawNative.selected PV_B2_F_ResourceFamilies.selected
set_option allowUnsafeReducibility true in
attribute [local irreducible] ProverRwP6BoundaryInstall.selected
open Aeneas Aeneas.Std Result ProverRwFull PV_RunJoin_WeightInstalled46

theorem first (u : Usize) (bound : u.val<262144) :
    (Usize.wrapping_mul 4#usize u).val=4*u.val := by
  rw [Usize.wrapping_mul_val_eq]
  change (4*u.val)%UScalar.size .Usize=4*u.val
  exact Nat.mod_eq_of_lt (by have h := PV_RunJoin_SamplerByteIndices54.size;omega)

theorem offset (u k : Usize) (bound : u.val<262144) (small : k.val<4) :
    (Usize.wrapping_add (Usize.wrapping_mul 4#usize u) k).val<1048576 := by
  rw [Usize.wrapping_add_val_eq,first u bound]
  change (4*u.val+k.val)%UScalar.size .Usize<1048576
  exact Nat.lt_of_le_of_lt (Nat.mod_le _ _) (by omega)

theorem complete (base : ExternalTypes) (heap : Heap) (box : Box)
    (ops : @ExternalFuns (types base)) (word : host_commitment.Word)
    (size : 1048576≤PV_RunJoin_QueryWordTotal64.length word)
    (u : aspis_core.r0.domain.FibreIndex) (bound : u.val<262144) :
    ∃ row, @host_commitment.opening_lane_values (types base) (selected base heap box ops) word u=ok row := by
  letI : ExternalTypes := types base
  letI : ExternalFuns := selected base heap box ops
  let at1 := Usize.wrapping_mul 4#usize u
  have h0 : at1.val<1048576 := by dsimp only [at1];rw [first u bound];omega
  obtain ⟨w0,h0⟩ := PV_RunJoin_QueryWordTotal64.complete base heap box ops word at1 (by omega)
  obtain ⟨w1,h1⟩ := PV_RunJoin_QueryWordTotal64.complete base heap box ops word
    (Usize.wrapping_add at1 1#usize) (Nat.lt_of_lt_of_le (offset u 1#usize bound (by decide)) size)
  obtain ⟨w2,h2⟩ := PV_RunJoin_QueryWordTotal64.complete base heap box ops word
    (Usize.wrapping_add at1 2#usize) (Nat.lt_of_lt_of_le (offset u 2#usize bound (by decide)) size)
  obtain ⟨w3,h3⟩ := PV_RunJoin_QueryWordTotal64.complete base heap box ops word
    (Usize.wrapping_add at1 3#usize) (Nat.lt_of_lt_of_le (offset u 3#usize bound (by decide)) size)
  refine ⟨Array.make 4#usize [w0,w1,w2,w3],?_⟩
  unfold host_commitment.opening_lane_values
  change (do let i ← (selected base heap box ops).op76 u
             let a ← Aeneas.Std.lift (Usize.wrapping_mul 4#usize i)
             let w0 ← host_commitment.Word.value word a
             let b ← Aeneas.Std.lift (Usize.wrapping_add a 1#usize)
             let w1 ← host_commitment.Word.value word b
             let c ← Aeneas.Std.lift (Usize.wrapping_add a 2#usize)
             let w2 ← host_commitment.Word.value word c
             let d ← Aeneas.Std.lift (Usize.wrapping_add a 3#usize)
             let w3 ← host_commitment.Word.value word d
             ok (Array.make 4#usize [w0,w1,w2,w3]))=_
  rw [PV_RunJoin_QueryHead63.get]
  simp only [ProverRwDictionaryDomain.fibreGet,lift,bind_tc_ok,h0,h1,h2,h3]

#print axioms first
#print axioms offset
#print axioms complete
end R1Z.PV_RunJoin_QueryLaneTotal64
