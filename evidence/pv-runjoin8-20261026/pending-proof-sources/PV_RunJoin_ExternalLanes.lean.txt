import R1Z.PV_RunJoin_ExternalSums
set_option autoImplicit false
namespace R1Z.PV_RunJoin_ExternalLanes
open Aeneas Aeneas.Std Result R0Z.WriterRefine R0Z.PoseidonRefine
open BuilderRecordsArray
abbrev State := Array U32 16#usize

def value (original : State) (j : Nat) : U32 :=
  PV_Src_ScalarReduce.value (U64.wrapping_add (UScalar.cast .U64 original.val[j]!)
    (PV_RunJoin_ExternalSums.target original).val[j%4]!)

def target (original : State) : State := tabulate 16#usize (value original)

def Suffix (original current : State) (lane : Usize) : Prop :=
  ∀ j, j < 16 → lane.val ≤ j → current.val[j]! = original.val[j]!

theorem loop (original current : State) (lane : Usize) (hl : lane.val ≤ 16)
    (prior : Prefix current (target original) lane.val)
    (suffix : Suffix original current lane) :
    AspisBuilderPoseidonReference.poseidon2.builder_reference.external_owned_loop2 current
      (PV_RunJoin_ExternalSums.target original) lane = ok (target original) := by
  generalize he : 16-lane.val = remaining
  induction remaining using Nat.strong_induction_on generalizing current lane with
  | h remaining ih =>
    rw [AspisBuilderPoseidonReference.poseidon2.builder_reference.external_owned_loop2]
    by_cases hit : lane.val < 16
    · rw [if_pos (by simpa [UScalar.lt_equiv] using hit),index_ok current lane (by simpa using hit)]
      simp only [lift,bind_tc_ok]
      rw [suffix lane.val hit (by omega),rem_ok lane 4#usize (by simp)]
      simp only [bind_tc_ok]
      have hm : (⟨BitVec.umod lane.bv (4#usize : Usize).bv⟩ : Usize).val < 4 := by
        rw [umod_val]
        exact Nat.mod_lt _ (by decide)
      rw [index_ok_gen (PV_RunJoin_ExternalSums.target original) _ (by simpa using hm)]
      simp only [lift,bind_tc_ok]
      rw [PV_Src_ScalarReduce.reference_eq]
      simp only [bind_tc_ok]
      rw [update_ok _ lane _ (by simpa using hit)]
      simp only [lift,bind_tc_ok,umod_val,UScalar.ofNatCore_val_eq]
      change AspisBuilderPoseidonReference.poseidon2.builder_reference.external_owned_loop2
        (current.set lane (value original lane.val)) (PV_RunJoin_ExternalSums.target original)
        (Usize.wrapping_add lane 1#usize) = _
      have hv : value original lane.val = (target original).val[lane.val]! :=
        (tabulate_get _ _ _ (by simpa using hit)).symm
      rw [hv]
      have hn := next_val lane (by omega)
      apply ih (16-(Usize.wrapping_add lane 1#usize).val) (by omega)
        _ (Usize.wrapping_add lane 1#usize) (by omega)
      · simpa only [hn] using prefix_step current (target original) lane (by simpa using hit) prior
      · intro j hj hafter
        rw [BuilderRecordsArray.set_get _ _ _ _ (by simpa using hit),if_neg (by rw [hn] at hafter;omega)]
        exact suffix j hj (by rw [hn] at hafter;omega)
      · rfl
    · rw [if_neg (by simpa [UScalar.lt_equiv] using hit)]
      have equal : lane.val = (16#usize : Usize).val := by simp;omega
      rw [prefix_done current (target original) (by simpa only [equal] using prior)]

theorem entry (original : State) :
    AspisBuilderPoseidonReference.poseidon2.builder_reference.external_owned_loop2 original
      (PV_RunJoin_ExternalSums.target original) 0#usize = ok (target original) :=
  loop original original 0#usize (by simp) (by intro j hj;simp at hj) (fun _ _ _ => rfl)

theorem canonical (original : State) (j : Nat) (hj : j < 16) :
    ((target original).val[j]!).val < 2147483647 := by
  rw [target,tabulate_get _ _ _ (by simpa using hj)]
  exact PV_Src_ScalarReduce.canonical _

/-- The U64 addition cannot wrap: each term is one U32 plus four U32s. -/
theorem field_value {K : Type} [Field K] [CharP K 2147483647]
    (original : State) (j : Nat) (hj : j < 16) :
    liftU (K := K) (target original).val[j]! =
      liftN original j +
        (((PV_RunJoin_ExternalSums.target original).val[j%4]!).val : K) := by
  have hm : j%4 < (4#usize : Usize).val := by simpa using Nat.mod_lt j (by decide : 0 < 4)
  have hs : ((PV_RunJoin_ExternalSums.target original).val[j%4]!).val =
      original.val[j%4]!.val + original.val[j%4+4]!.val +
        original.val[j%4+8]!.val + original.val[j%4+12]!.val := by
    rw [PV_RunJoin_ExternalSums.target,tabulate_get _ _ _ hm,PV_RunJoin_ExternalSums.word_value]
  have bound : original.val[j]!.val + ((PV_RunJoin_ExternalSums.target original).val[j%4]!).val <
      18446744073709551616 := by
    rw [hs]
    have := u32lt original.val[j]!
    have := u32lt original.val[j%4]!
    have := u32lt original.val[j%4+4]!
    have := u32lt original.val[j%4+8]!
    have := u32lt original.val[j%4+12]!
    omega
  have added := add64v (UScalar.cast .U64 original.val[j]!)
    (PV_RunJoin_ExternalSums.target original).val[j%4]!
    original.val[j]!.val ((PV_RunJoin_ExternalSums.target original).val[j%4]!).val
    (c64 _) rfl bound
  rw [target,tabulate_get _ _ _ (by simpa using hj)]
  change ((PV_Src_ScalarReduce.value _).val : K) = _
  rw [PV_Src_ScalarReduce.modulo,cast_mod,added]
  simp only [Nat.cast_add,liftN,liftU]

#print axioms loop
#print axioms entry
#print axioms canonical
#print axioms field_value
end R1Z.PV_RunJoin_ExternalLanes
