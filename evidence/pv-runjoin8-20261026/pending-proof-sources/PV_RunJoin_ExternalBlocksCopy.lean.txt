import R1Z.PV_RunJoin_SourceArithmeticLift
import R1Z.BuilderRecordsArray
set_option autoImplicit false
namespace R1Z.PV_RunJoin_ExternalBlocksCopy
open Aeneas Aeneas.Std Result R0Z.WriterRefine R0Z.PoseidonRefine
open BuilderRecordsArray
abbrev State := Array U32 16#usize

/-- Unprocessed lanes still hold the original source words. The source writes
its four matrix outputs in-place; the checked copy reads a separate original
array. This suffix invariant makes that difference explicit. -/
def Suffix (original state : State) (block : Usize) : Prop :=
  ∀ j, j < 16 → 4*block.val ≤ j → state.val[j]! = original.val[j]!

theorem loop (original state : State) (block : Usize) (hb : block.val ≤ 4)
    (suffix : Suffix original state block) :
    AspisBuilderPoseidonReference.poseidon2.builder_reference.external_owned_loop0 state block =
      R0PoseidonCopy.ext_groups_loop original state block := by
  generalize he : 4-block.val = remaining
  induction remaining using Nat.strong_induction_on generalizing state block with
  | h remaining ih =>
    rw [AspisBuilderPoseidonReference.poseidon2.builder_reference.external_owned_loop0,
      R0PoseidonCopy.ext_groups_loop]
    by_cases hit : block.val < 4
    · have hlt : block < 4#usize := by simpa [UScalar.lt_equiv] using hit
      simp only [if_pos hlt]
      have mulcomm : Usize.wrapping_mul block 4#usize = Usize.wrapping_mul 4#usize block := by
        apply UScalar.eq_of_val_eq
        rw [umul _ _ (by simp;omega),umul _ _ (by simp;omega)]
        simp only [UScalar.ofNatCore_val_eq]
        omega
      rw [mulcomm]
      simp only [lift,bind_tc_ok]
      let i0 := Usize.wrapping_mul 4#usize block
      let i1 := Usize.wrapping_add i0 1#usize
      let i2 := Usize.wrapping_add i0 2#usize
      let i3 := Usize.wrapping_add i0 3#usize
      have h0 : i0.val = 4*block.val := by
        dsimp only [i0]
        rw [umul _ _ (by simp;omega)]
        rfl
      have h1 : i1.val = 4*block.val+1 := by
        dsimp only [i1]
        rw [uadd _ _ (by rw [h0];simp;omega),h0]
        rfl
      have h2 : i2.val = 4*block.val+2 := by
        dsimp only [i2]
        rw [uadd _ _ (by rw [h0];simp;omega),h0]
        rfl
      have h3 : i3.val = 4*block.val+3 := by
        dsimp only [i3]
        rw [uadd _ _ (by rw [h0];simp;omega),h0]
        rfl
      have b0 : i0.val < (16#usize : Usize).val := by rw [h0];simp;omega
      have b1 : i1.val < (16#usize : Usize).val := by rw [h1];simp;omega
      have b2 : i2.val < (16#usize : Usize).val := by rw [h2];simp;omega
      have b3 : i3.val < (16#usize : Usize).val := by rw [h3];simp;omega
      have s0 := suffix i0.val (by simpa using b0) (by omega)
      have s1 := suffix i1.val (by simpa using b1) (by rw [h1];omega)
      have s2 := suffix i2.val (by simpa using b2) (by rw [h2];omega)
      have s3 := suffix i3.val (by simpa using b3) (by rw [h3];omega)
      rw [index_ok state i0 b0]
      simp only [lift,bind_tc_ok]
      rw [index_ok state i1 b1]
      simp only [lift,bind_tc_ok]
      rw [index_ok state i2 b2]
      simp only [lift,bind_tc_ok]
      rw [index_ok state i3 b3]
      simp only [lift,bind_tc_ok]
      rw [index_ok original i0 b0]
      simp only [lift,bind_tc_ok]
      rw [index_ok original i1 b1]
      simp only [lift,bind_tc_ok]
      rw [index_ok original i2 b2]
      simp only [lift,bind_tc_ok]
      rw [index_ok original i3 b3]
      simp only [lift,bind_tc_ok]
      rw [s0,s1,s2,s3]
      rw [PV_Src_ExternalMat4Copy.equals_copy]
      apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
      intro m hm
      have u0 : ∀ (v : State) x, Array.update v i0 x = ok (v.set i0 x) := fun v x => update_ok v i0 x b0
      have u1 : ∀ (v : State) x, Array.update v i1 x = ok (v.set i1 x) := fun v x => update_ok v i1 x b1
      have u2 : ∀ (v : State) x, Array.update v i2 x = ok (v.set i2 x) := fun v x => update_ok v i2 x b2
      have u3 : ∀ (v : State) x, Array.update v i3 x = ok (v.set i3 x) := fun v x => update_ok v i3 x b3
      simp only [index_ok m 0#usize (by decide),index_ok m 1#usize (by decide),
        index_ok m 2#usize (by decide),index_ok m 3#usize (by decide),bind_tc_ok]
      rw [u0]
      simp only [bind_tc_ok]
      rw [u1]
      simp only [bind_tc_ok]
      rw [u2]
      simp only [bind_tc_ok]
      rw [u3]
      simp only [bind_tc_ok]
      have hn := next_val block (by omega)
      apply ih (4-(Usize.wrapping_add block 1#usize).val) (by omega)
        _ (Usize.wrapping_add block 1#usize) (by omega)
      · intro j hj hafter
        have ne0 : j ≠ i0.val := by rw [h0];rw [hn] at hafter;omega
        have ne1 : j ≠ i1.val := by rw [h1];rw [hn] at hafter;omega
        have ne2 : j ≠ i2.val := by rw [h2];rw [hn] at hafter;omega
        have ne3 : j ≠ i3.val := by rw [h3];rw [hn] at hafter;omega
        rw [set_get _ _ _ _ b3,if_neg ne3,set_get _ _ _ _ b2,if_neg ne2,
          set_get _ _ _ _ b1,if_neg ne1,set_get _ _ _ _ b0,if_neg ne0]
        exact suffix j hj (by rw [hn] at hafter;omega)
      · rfl
    · have hlt : ¬ block < 4#usize := by simpa [UScalar.lt_equiv] using hit
      simp only [if_neg hlt]

/-- At entry no suffix hypothesis is required: every word is still original.
The checked copy's totality and field-content facts can therefore be reused
for this in-place source stage without any canonical-input premise. -/
theorem entry (state : State) :
    AspisBuilderPoseidonReference.poseidon2.builder_reference.external_owned_loop0 state 0#usize =
      R0PoseidonCopy.ext_groups_loop state state 0#usize :=
  loop state state 0#usize (by simp) (fun _ _ _ => rfl)

/-- Full field content of all four source matrix blocks follows from the
checked copy induction, without any input canonicality or execution premise. -/
theorem field_entry {K : Type} [Field K] [CharP K 2147483647] (state : State) :
    ∃ out,
      AspisBuilderPoseidonReference.poseidon2.builder_reference.external_owned_loop0 state 0#usize = ok out ∧
      ∀ g c : Fin 4, liftU (K := K) out.val[4*g.val+c.val]! = PM state g c := by
  obtain ⟨out,run,meaning,_⟩ := R0Z.PoseidonRefine.groups_loop (K := K)
    state 4 0#usize state (by simp)
  refine ⟨out,(entry state).trans run,?_⟩
  intro g c
  exact meaning g.val c.val g.isLt c.isLt (by simp)

#print axioms loop
#print axioms entry
#print axioms field_entry
end R1Z.PV_RunJoin_ExternalBlocksCopy
