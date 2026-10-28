import R1Z.PV_RunJoin_IndexedRound0019
import R1Z.PV_RunJoin_IndexedRound0119
import R1Z.PV_RunJoin_IndexedRound0219
import R1Z.PV_RunJoin_IndexedRound0319
import R1Z.PV_RunJoin_IndexedRound0419
import R1Z.PV_RunJoin_IndexedRound0519
import R1Z.PV_RunJoin_IndexedRound0619
import R1Z.PV_RunJoin_IndexedRound0719
import R1Z.PV_RunJoin_IndexedRound0819
import R1Z.PV_RunJoin_IndexedRound0919
import R1Z.PV_RunJoin_IndexedRound1019
import R1Z.PV_RunJoin_IndexedRound1119
import R1Z.PV_RunJoin_IndexedRound1219
import R1Z.PV_RunJoin_IndexedRound1319
import R1Z.PV_RunJoin_IndexedRound1419
import R1Z.PV_RunJoin_IndexedRound1519
import R1Z.PV_RunJoin_IndexedRound1619
import R1Z.PV_RunJoin_IndexedRound1719
import R1Z.PV_RunJoin_IndexedRound1819
import R1Z.PV_RunJoin_IndexedRound1919
import R1Z.PV_RunJoin_IndexedRound2019
import R1Z.PV_RunJoin_IndexedRound2119
import R1Z.PV_Src_PortInitialConstants
import R1Z.PV_Src_PortInternalConstants
import R1Z.PV_Src_PortFinalConstants
set_option autoImplicit false
namespace R1Z.PV_RunJoin_IndexedCopy19
open Aeneas Aeneas.Std Result R0Z.WriterRefine R0Z.PoseidonRefine
open BuilderForestStdPort BuilderForestAdmissionPort PV_Src_PortSboxStep
local instance : ExternalLinear := PV_Src_ExternalReference.dictionary
theorem copy00 (s : State) (hs : Canonical s) :
    poseidon2.apply_round_by_index s 0#usize =
      (do let out ← R0PoseidonCopy.apply_round s 0#usize; ok (some (),out)) := by
  rw [PV_RunJoin_IndexedRound0019.source s hs (PV_Src_PortInitialConstants.canonical ⟨0,by decide⟩)]
  rw [PV_Src_PortTables.initial]
  have hc : R0PoseidonCopy.apply_round s 0#usize = R0PoseidonCopy.full_round s R0PoseidonCopy.EXTERNAL_INITIAL.val[0]! := by
    rw [R0PoseidonCopy.apply_round]
    rw [if_pos (by decide)]
    have hk : Array.index_usize R0PoseidonCopy.EXTERNAL_INITIAL 0#usize = ok R0PoseidonCopy.EXTERNAL_INITIAL.val[0]! := by
      with_unfolding_all rfl
    rw [hk]
    rfl
  rw [hc]
#print axioms copy00
theorem copy01 (s : State) (hs : Canonical s) :
    poseidon2.apply_round_by_index s 1#usize =
      (do let out ← R0PoseidonCopy.apply_round s 1#usize; ok (some (),out)) := by
  rw [PV_RunJoin_IndexedRound0119.source s hs (PV_Src_PortInitialConstants.canonical ⟨1,by decide⟩)]
  rw [PV_Src_PortTables.initial]
  have hc : R0PoseidonCopy.apply_round s 1#usize = R0PoseidonCopy.full_round s R0PoseidonCopy.EXTERNAL_INITIAL.val[1]! := by
    rw [R0PoseidonCopy.apply_round]
    rw [if_pos (by decide)]
    have hk : Array.index_usize R0PoseidonCopy.EXTERNAL_INITIAL 1#usize = ok R0PoseidonCopy.EXTERNAL_INITIAL.val[1]! := by
      with_unfolding_all rfl
    rw [hk]
    rfl
  rw [hc]
#print axioms copy01
theorem copy02 (s : State) (hs : Canonical s) :
    poseidon2.apply_round_by_index s 2#usize =
      (do let out ← R0PoseidonCopy.apply_round s 2#usize; ok (some (),out)) := by
  rw [PV_RunJoin_IndexedRound0219.source s hs (PV_Src_PortInitialConstants.canonical ⟨2,by decide⟩)]
  rw [PV_Src_PortTables.initial]
  have hc : R0PoseidonCopy.apply_round s 2#usize = R0PoseidonCopy.full_round s R0PoseidonCopy.EXTERNAL_INITIAL.val[2]! := by
    rw [R0PoseidonCopy.apply_round]
    rw [if_pos (by decide)]
    have hk : Array.index_usize R0PoseidonCopy.EXTERNAL_INITIAL 2#usize = ok R0PoseidonCopy.EXTERNAL_INITIAL.val[2]! := by
      with_unfolding_all rfl
    rw [hk]
    rfl
  rw [hc]
#print axioms copy02
theorem copy03 (s : State) (hs : Canonical s) :
    poseidon2.apply_round_by_index s 3#usize =
      (do let out ← R0PoseidonCopy.apply_round s 3#usize; ok (some (),out)) := by
  rw [PV_RunJoin_IndexedRound0319.source s hs (PV_Src_PortInitialConstants.canonical ⟨3,by decide⟩)]
  rw [PV_Src_PortTables.initial]
  have hc : R0PoseidonCopy.apply_round s 3#usize = R0PoseidonCopy.full_round s R0PoseidonCopy.EXTERNAL_INITIAL.val[3]! := by
    rw [R0PoseidonCopy.apply_round]
    rw [if_pos (by decide)]
    have hk : Array.index_usize R0PoseidonCopy.EXTERNAL_INITIAL 3#usize = ok R0PoseidonCopy.EXTERNAL_INITIAL.val[3]! := by
      with_unfolding_all rfl
    rw [hk]
    rfl
  rw [hc]
#print axioms copy03
theorem copy04 (s : State) (hs : Canonical s) :
    poseidon2.apply_round_by_index s 4#usize =
      (do let out ← R0PoseidonCopy.apply_round s 4#usize; ok (some (),out)) := by
  rw [PV_RunJoin_IndexedRound0419.source s hs (PV_Src_PortInternalConstants.canonical ⟨0,by decide⟩)]
  rw [PV_Src_PortTables.internal]
  have hc : R0PoseidonCopy.apply_round s 4#usize = R0PoseidonCopy.internal_round s R0PoseidonCopy.INTERNAL.val[0]! R0PoseidonCopy.INTERNAL_SHIFTS := by
    rw [R0PoseidonCopy.apply_round]
    rw [if_neg (by decide)]
    rw [if_pos (by decide)]
    simp only [lift,bind_tc_ok]
    have hi : Usize.wrapping_sub 4#usize 4#usize = 0#usize := by
      apply UScalar.eq_of_val_eq
      rw [R0Z.WriterRefine.usub _ _ (by simp)]
      rfl
    rw [hi]
    have hk : Array.index_usize R0PoseidonCopy.INTERNAL 0#usize = ok R0PoseidonCopy.INTERNAL.val[0]! := by
      with_unfolding_all rfl
    rw [hk]
    rfl
  rw [hc]
#print axioms copy04
theorem copy05 (s : State) (hs : Canonical s) :
    poseidon2.apply_round_by_index s 5#usize =
      (do let out ← R0PoseidonCopy.apply_round s 5#usize; ok (some (),out)) := by
  rw [PV_RunJoin_IndexedRound0519.source s hs (PV_Src_PortInternalConstants.canonical ⟨1,by decide⟩)]
  rw [PV_Src_PortTables.internal]
  have hc : R0PoseidonCopy.apply_round s 5#usize = R0PoseidonCopy.internal_round s R0PoseidonCopy.INTERNAL.val[1]! R0PoseidonCopy.INTERNAL_SHIFTS := by
    rw [R0PoseidonCopy.apply_round]
    rw [if_neg (by decide)]
    rw [if_pos (by decide)]
    simp only [lift,bind_tc_ok]
    have hi : Usize.wrapping_sub 5#usize 4#usize = 1#usize := by
      apply UScalar.eq_of_val_eq
      rw [R0Z.WriterRefine.usub _ _ (by simp)]
      rfl
    rw [hi]
    have hk : Array.index_usize R0PoseidonCopy.INTERNAL 1#usize = ok R0PoseidonCopy.INTERNAL.val[1]! := by
      with_unfolding_all rfl
    rw [hk]
    rfl
  rw [hc]
#print axioms copy05
theorem copy06 (s : State) (hs : Canonical s) :
    poseidon2.apply_round_by_index s 6#usize =
      (do let out ← R0PoseidonCopy.apply_round s 6#usize; ok (some (),out)) := by
  rw [PV_RunJoin_IndexedRound0619.source s hs (PV_Src_PortInternalConstants.canonical ⟨2,by decide⟩)]
  rw [PV_Src_PortTables.internal]
  have hc : R0PoseidonCopy.apply_round s 6#usize = R0PoseidonCopy.internal_round s R0PoseidonCopy.INTERNAL.val[2]! R0PoseidonCopy.INTERNAL_SHIFTS := by
    rw [R0PoseidonCopy.apply_round]
    rw [if_neg (by decide)]
    rw [if_pos (by decide)]
    simp only [lift,bind_tc_ok]
    have hi : Usize.wrapping_sub 6#usize 4#usize = 2#usize := by
      apply UScalar.eq_of_val_eq
      rw [R0Z.WriterRefine.usub _ _ (by simp)]
      rfl
    rw [hi]
    have hk : Array.index_usize R0PoseidonCopy.INTERNAL 2#usize = ok R0PoseidonCopy.INTERNAL.val[2]! := by
      with_unfolding_all rfl
    rw [hk]
    rfl
  rw [hc]
#print axioms copy06
theorem copy07 (s : State) (hs : Canonical s) :
    poseidon2.apply_round_by_index s 7#usize =
      (do let out ← R0PoseidonCopy.apply_round s 7#usize; ok (some (),out)) := by
  rw [PV_RunJoin_IndexedRound0719.source s hs (PV_Src_PortInternalConstants.canonical ⟨3,by decide⟩)]
  rw [PV_Src_PortTables.internal]
  have hc : R0PoseidonCopy.apply_round s 7#usize = R0PoseidonCopy.internal_round s R0PoseidonCopy.INTERNAL.val[3]! R0PoseidonCopy.INTERNAL_SHIFTS := by
    rw [R0PoseidonCopy.apply_round]
    rw [if_neg (by decide)]
    rw [if_pos (by decide)]
    simp only [lift,bind_tc_ok]
    have hi : Usize.wrapping_sub 7#usize 4#usize = 3#usize := by
      apply UScalar.eq_of_val_eq
      rw [R0Z.WriterRefine.usub _ _ (by simp)]
      rfl
    rw [hi]
    have hk : Array.index_usize R0PoseidonCopy.INTERNAL 3#usize = ok R0PoseidonCopy.INTERNAL.val[3]! := by
      with_unfolding_all rfl
    rw [hk]
    rfl
  rw [hc]
#print axioms copy07
theorem copy08 (s : State) (hs : Canonical s) :
    poseidon2.apply_round_by_index s 8#usize =
      (do let out ← R0PoseidonCopy.apply_round s 8#usize; ok (some (),out)) := by
  rw [PV_RunJoin_IndexedRound0819.source s hs (PV_Src_PortInternalConstants.canonical ⟨4,by decide⟩)]
  rw [PV_Src_PortTables.internal]
  have hc : R0PoseidonCopy.apply_round s 8#usize = R0PoseidonCopy.internal_round s R0PoseidonCopy.INTERNAL.val[4]! R0PoseidonCopy.INTERNAL_SHIFTS := by
    rw [R0PoseidonCopy.apply_round]
    rw [if_neg (by decide)]
    rw [if_pos (by decide)]
    simp only [lift,bind_tc_ok]
    have hi : Usize.wrapping_sub 8#usize 4#usize = 4#usize := by
      apply UScalar.eq_of_val_eq
      rw [R0Z.WriterRefine.usub _ _ (by simp)]
      rfl
    rw [hi]
    have hk : Array.index_usize R0PoseidonCopy.INTERNAL 4#usize = ok R0PoseidonCopy.INTERNAL.val[4]! := by
      with_unfolding_all rfl
    rw [hk]
    rfl
  rw [hc]
#print axioms copy08
theorem copy09 (s : State) (hs : Canonical s) :
    poseidon2.apply_round_by_index s 9#usize =
      (do let out ← R0PoseidonCopy.apply_round s 9#usize; ok (some (),out)) := by
  rw [PV_RunJoin_IndexedRound0919.source s hs (PV_Src_PortInternalConstants.canonical ⟨5,by decide⟩)]
  rw [PV_Src_PortTables.internal]
  have hc : R0PoseidonCopy.apply_round s 9#usize = R0PoseidonCopy.internal_round s R0PoseidonCopy.INTERNAL.val[5]! R0PoseidonCopy.INTERNAL_SHIFTS := by
    rw [R0PoseidonCopy.apply_round]
    rw [if_neg (by decide)]
    rw [if_pos (by decide)]
    simp only [lift,bind_tc_ok]
    have hi : Usize.wrapping_sub 9#usize 4#usize = 5#usize := by
      apply UScalar.eq_of_val_eq
      rw [R0Z.WriterRefine.usub _ _ (by simp)]
      rfl
    rw [hi]
    have hk : Array.index_usize R0PoseidonCopy.INTERNAL 5#usize = ok R0PoseidonCopy.INTERNAL.val[5]! := by
      with_unfolding_all rfl
    rw [hk]
    rfl
  rw [hc]
#print axioms copy09
theorem copy10 (s : State) (hs : Canonical s) :
    poseidon2.apply_round_by_index s 10#usize =
      (do let out ← R0PoseidonCopy.apply_round s 10#usize; ok (some (),out)) := by
  rw [PV_RunJoin_IndexedRound1019.source s hs (PV_Src_PortInternalConstants.canonical ⟨6,by decide⟩)]
  rw [PV_Src_PortTables.internal]
  have hc : R0PoseidonCopy.apply_round s 10#usize = R0PoseidonCopy.internal_round s R0PoseidonCopy.INTERNAL.val[6]! R0PoseidonCopy.INTERNAL_SHIFTS := by
    rw [R0PoseidonCopy.apply_round]
    rw [if_neg (by decide)]
    rw [if_pos (by decide)]
    simp only [lift,bind_tc_ok]
    have hi : Usize.wrapping_sub 10#usize 4#usize = 6#usize := by
      apply UScalar.eq_of_val_eq
      rw [R0Z.WriterRefine.usub _ _ (by simp)]
      rfl
    rw [hi]
    have hk : Array.index_usize R0PoseidonCopy.INTERNAL 6#usize = ok R0PoseidonCopy.INTERNAL.val[6]! := by
      with_unfolding_all rfl
    rw [hk]
    rfl
  rw [hc]
#print axioms copy10
theorem copy11 (s : State) (hs : Canonical s) :
    poseidon2.apply_round_by_index s 11#usize =
      (do let out ← R0PoseidonCopy.apply_round s 11#usize; ok (some (),out)) := by
  rw [PV_RunJoin_IndexedRound1119.source s hs (PV_Src_PortInternalConstants.canonical ⟨7,by decide⟩)]
  rw [PV_Src_PortTables.internal]
  have hc : R0PoseidonCopy.apply_round s 11#usize = R0PoseidonCopy.internal_round s R0PoseidonCopy.INTERNAL.val[7]! R0PoseidonCopy.INTERNAL_SHIFTS := by
    rw [R0PoseidonCopy.apply_round]
    rw [if_neg (by decide)]
    rw [if_pos (by decide)]
    simp only [lift,bind_tc_ok]
    have hi : Usize.wrapping_sub 11#usize 4#usize = 7#usize := by
      apply UScalar.eq_of_val_eq
      rw [R0Z.WriterRefine.usub _ _ (by simp)]
      rfl
    rw [hi]
    have hk : Array.index_usize R0PoseidonCopy.INTERNAL 7#usize = ok R0PoseidonCopy.INTERNAL.val[7]! := by
      with_unfolding_all rfl
    rw [hk]
    rfl
  rw [hc]
#print axioms copy11
theorem copy12 (s : State) (hs : Canonical s) :
    poseidon2.apply_round_by_index s 12#usize =
      (do let out ← R0PoseidonCopy.apply_round s 12#usize; ok (some (),out)) := by
  rw [PV_RunJoin_IndexedRound1219.source s hs (PV_Src_PortInternalConstants.canonical ⟨8,by decide⟩)]
  rw [PV_Src_PortTables.internal]
  have hc : R0PoseidonCopy.apply_round s 12#usize = R0PoseidonCopy.internal_round s R0PoseidonCopy.INTERNAL.val[8]! R0PoseidonCopy.INTERNAL_SHIFTS := by
    rw [R0PoseidonCopy.apply_round]
    rw [if_neg (by decide)]
    rw [if_pos (by decide)]
    simp only [lift,bind_tc_ok]
    have hi : Usize.wrapping_sub 12#usize 4#usize = 8#usize := by
      apply UScalar.eq_of_val_eq
      rw [R0Z.WriterRefine.usub _ _ (by simp)]
      rfl
    rw [hi]
    have hk : Array.index_usize R0PoseidonCopy.INTERNAL 8#usize = ok R0PoseidonCopy.INTERNAL.val[8]! := by
      with_unfolding_all rfl
    rw [hk]
    rfl
  rw [hc]
#print axioms copy12
theorem copy13 (s : State) (hs : Canonical s) :
    poseidon2.apply_round_by_index s 13#usize =
      (do let out ← R0PoseidonCopy.apply_round s 13#usize; ok (some (),out)) := by
  rw [PV_RunJoin_IndexedRound1319.source s hs (PV_Src_PortInternalConstants.canonical ⟨9,by decide⟩)]
  rw [PV_Src_PortTables.internal]
  have hc : R0PoseidonCopy.apply_round s 13#usize = R0PoseidonCopy.internal_round s R0PoseidonCopy.INTERNAL.val[9]! R0PoseidonCopy.INTERNAL_SHIFTS := by
    rw [R0PoseidonCopy.apply_round]
    rw [if_neg (by decide)]
    rw [if_pos (by decide)]
    simp only [lift,bind_tc_ok]
    have hi : Usize.wrapping_sub 13#usize 4#usize = 9#usize := by
      apply UScalar.eq_of_val_eq
      rw [R0Z.WriterRefine.usub _ _ (by simp)]
      rfl
    rw [hi]
    have hk : Array.index_usize R0PoseidonCopy.INTERNAL 9#usize = ok R0PoseidonCopy.INTERNAL.val[9]! := by
      with_unfolding_all rfl
    rw [hk]
    rfl
  rw [hc]
#print axioms copy13
theorem copy14 (s : State) (hs : Canonical s) :
    poseidon2.apply_round_by_index s 14#usize =
      (do let out ← R0PoseidonCopy.apply_round s 14#usize; ok (some (),out)) := by
  rw [PV_RunJoin_IndexedRound1419.source s hs (PV_Src_PortInternalConstants.canonical ⟨10,by decide⟩)]
  rw [PV_Src_PortTables.internal]
  have hc : R0PoseidonCopy.apply_round s 14#usize = R0PoseidonCopy.internal_round s R0PoseidonCopy.INTERNAL.val[10]! R0PoseidonCopy.INTERNAL_SHIFTS := by
    rw [R0PoseidonCopy.apply_round]
    rw [if_neg (by decide)]
    rw [if_pos (by decide)]
    simp only [lift,bind_tc_ok]
    have hi : Usize.wrapping_sub 14#usize 4#usize = 10#usize := by
      apply UScalar.eq_of_val_eq
      rw [R0Z.WriterRefine.usub _ _ (by simp)]
      rfl
    rw [hi]
    have hk : Array.index_usize R0PoseidonCopy.INTERNAL 10#usize = ok R0PoseidonCopy.INTERNAL.val[10]! := by
      with_unfolding_all rfl
    rw [hk]
    rfl
  rw [hc]
#print axioms copy14
theorem copy15 (s : State) (hs : Canonical s) :
    poseidon2.apply_round_by_index s 15#usize =
      (do let out ← R0PoseidonCopy.apply_round s 15#usize; ok (some (),out)) := by
  rw [PV_RunJoin_IndexedRound1519.source s hs (PV_Src_PortInternalConstants.canonical ⟨11,by decide⟩)]
  rw [PV_Src_PortTables.internal]
  have hc : R0PoseidonCopy.apply_round s 15#usize = R0PoseidonCopy.internal_round s R0PoseidonCopy.INTERNAL.val[11]! R0PoseidonCopy.INTERNAL_SHIFTS := by
    rw [R0PoseidonCopy.apply_round]
    rw [if_neg (by decide)]
    rw [if_pos (by decide)]
    simp only [lift,bind_tc_ok]
    have hi : Usize.wrapping_sub 15#usize 4#usize = 11#usize := by
      apply UScalar.eq_of_val_eq
      rw [R0Z.WriterRefine.usub _ _ (by simp)]
      rfl
    rw [hi]
    have hk : Array.index_usize R0PoseidonCopy.INTERNAL 11#usize = ok R0PoseidonCopy.INTERNAL.val[11]! := by
      with_unfolding_all rfl
    rw [hk]
    rfl
  rw [hc]
#print axioms copy15
theorem copy16 (s : State) (hs : Canonical s) :
    poseidon2.apply_round_by_index s 16#usize =
      (do let out ← R0PoseidonCopy.apply_round s 16#usize; ok (some (),out)) := by
  rw [PV_RunJoin_IndexedRound1619.source s hs (PV_Src_PortInternalConstants.canonical ⟨12,by decide⟩)]
  rw [PV_Src_PortTables.internal]
  have hc : R0PoseidonCopy.apply_round s 16#usize = R0PoseidonCopy.internal_round s R0PoseidonCopy.INTERNAL.val[12]! R0PoseidonCopy.INTERNAL_SHIFTS := by
    rw [R0PoseidonCopy.apply_round]
    rw [if_neg (by decide)]
    rw [if_pos (by decide)]
    simp only [lift,bind_tc_ok]
    have hi : Usize.wrapping_sub 16#usize 4#usize = 12#usize := by
      apply UScalar.eq_of_val_eq
      rw [R0Z.WriterRefine.usub _ _ (by simp)]
      rfl
    rw [hi]
    have hk : Array.index_usize R0PoseidonCopy.INTERNAL 12#usize = ok R0PoseidonCopy.INTERNAL.val[12]! := by
      with_unfolding_all rfl
    rw [hk]
    rfl
  rw [hc]
#print axioms copy16
theorem copy17 (s : State) (hs : Canonical s) :
    poseidon2.apply_round_by_index s 17#usize =
      (do let out ← R0PoseidonCopy.apply_round s 17#usize; ok (some (),out)) := by
  rw [PV_RunJoin_IndexedRound1719.source s hs (PV_Src_PortInternalConstants.canonical ⟨13,by decide⟩)]
  rw [PV_Src_PortTables.internal]
  have hc : R0PoseidonCopy.apply_round s 17#usize = R0PoseidonCopy.internal_round s R0PoseidonCopy.INTERNAL.val[13]! R0PoseidonCopy.INTERNAL_SHIFTS := by
    rw [R0PoseidonCopy.apply_round]
    rw [if_neg (by decide)]
    rw [if_pos (by decide)]
    simp only [lift,bind_tc_ok]
    have hi : Usize.wrapping_sub 17#usize 4#usize = 13#usize := by
      apply UScalar.eq_of_val_eq
      rw [R0Z.WriterRefine.usub _ _ (by simp)]
      rfl
    rw [hi]
    have hk : Array.index_usize R0PoseidonCopy.INTERNAL 13#usize = ok R0PoseidonCopy.INTERNAL.val[13]! := by
      with_unfolding_all rfl
    rw [hk]
    rfl
  rw [hc]
#print axioms copy17
theorem copy18 (s : State) (hs : Canonical s) :
    poseidon2.apply_round_by_index s 18#usize =
      (do let out ← R0PoseidonCopy.apply_round s 18#usize; ok (some (),out)) := by
  rw [PV_RunJoin_IndexedRound1819.source s hs (PV_Src_PortFinalConstants.canonical ⟨0,by decide⟩)]
  rw [PV_Src_PortTables.final_constants]
  have hc : R0PoseidonCopy.apply_round s 18#usize = R0PoseidonCopy.full_round s R0PoseidonCopy.EXTERNAL_FINAL.val[0]! := by
    rw [R0PoseidonCopy.apply_round]
    rw [if_neg (by decide)]
    rw [if_neg (by decide)]
    simp only [lift,bind_tc_ok]
    have hi : Usize.wrapping_sub 18#usize 18#usize = 0#usize := by
      apply UScalar.eq_of_val_eq
      rw [R0Z.WriterRefine.usub _ _ (by simp)]
      rfl
    rw [hi]
    have hk : Array.index_usize R0PoseidonCopy.EXTERNAL_FINAL 0#usize = ok R0PoseidonCopy.EXTERNAL_FINAL.val[0]! := by
      with_unfolding_all rfl
    rw [hk]
    rfl
  rw [hc]
#print axioms copy18
theorem copy19 (s : State) (hs : Canonical s) :
    poseidon2.apply_round_by_index s 19#usize =
      (do let out ← R0PoseidonCopy.apply_round s 19#usize; ok (some (),out)) := by
  rw [PV_RunJoin_IndexedRound1919.source s hs (PV_Src_PortFinalConstants.canonical ⟨1,by decide⟩)]
  rw [PV_Src_PortTables.final_constants]
  have hc : R0PoseidonCopy.apply_round s 19#usize = R0PoseidonCopy.full_round s R0PoseidonCopy.EXTERNAL_FINAL.val[1]! := by
    rw [R0PoseidonCopy.apply_round]
    rw [if_neg (by decide)]
    rw [if_neg (by decide)]
    simp only [lift,bind_tc_ok]
    have hi : Usize.wrapping_sub 19#usize 18#usize = 1#usize := by
      apply UScalar.eq_of_val_eq
      rw [R0Z.WriterRefine.usub _ _ (by simp)]
      rfl
    rw [hi]
    have hk : Array.index_usize R0PoseidonCopy.EXTERNAL_FINAL 1#usize = ok R0PoseidonCopy.EXTERNAL_FINAL.val[1]! := by
      with_unfolding_all rfl
    rw [hk]
    rfl
  rw [hc]
#print axioms copy19
theorem copy20 (s : State) (hs : Canonical s) :
    poseidon2.apply_round_by_index s 20#usize =
      (do let out ← R0PoseidonCopy.apply_round s 20#usize; ok (some (),out)) := by
  rw [PV_RunJoin_IndexedRound2019.source s hs (PV_Src_PortFinalConstants.canonical ⟨2,by decide⟩)]
  rw [PV_Src_PortTables.final_constants]
  have hc : R0PoseidonCopy.apply_round s 20#usize = R0PoseidonCopy.full_round s R0PoseidonCopy.EXTERNAL_FINAL.val[2]! := by
    rw [R0PoseidonCopy.apply_round]
    rw [if_neg (by decide)]
    rw [if_neg (by decide)]
    simp only [lift,bind_tc_ok]
    have hi : Usize.wrapping_sub 20#usize 18#usize = 2#usize := by
      apply UScalar.eq_of_val_eq
      rw [R0Z.WriterRefine.usub _ _ (by simp)]
      rfl
    rw [hi]
    have hk : Array.index_usize R0PoseidonCopy.EXTERNAL_FINAL 2#usize = ok R0PoseidonCopy.EXTERNAL_FINAL.val[2]! := by
      with_unfolding_all rfl
    rw [hk]
    rfl
  rw [hc]
#print axioms copy20
theorem copy21 (s : State) (hs : Canonical s) :
    poseidon2.apply_round_by_index s 21#usize =
      (do let out ← R0PoseidonCopy.apply_round s 21#usize; ok (some (),out)) := by
  rw [PV_RunJoin_IndexedRound2119.source s hs (PV_Src_PortFinalConstants.canonical ⟨3,by decide⟩)]
  rw [PV_Src_PortTables.final_constants]
  have hc : R0PoseidonCopy.apply_round s 21#usize = R0PoseidonCopy.full_round s R0PoseidonCopy.EXTERNAL_FINAL.val[3]! := by
    rw [R0PoseidonCopy.apply_round]
    rw [if_neg (by decide)]
    rw [if_neg (by decide)]
    simp only [lift,bind_tc_ok]
    have hi : Usize.wrapping_sub 21#usize 18#usize = 3#usize := by
      apply UScalar.eq_of_val_eq
      rw [R0Z.WriterRefine.usub _ _ (by simp)]
      rfl
    rw [hi]
    have hk : Array.index_usize R0PoseidonCopy.EXTERNAL_FINAL 3#usize = ok R0PoseidonCopy.EXTERNAL_FINAL.val[3]! := by
      with_unfolding_all rfl
    rw [hk]
    rfl
  rw [hc]
#print axioms copy21
theorem source (s : State) (hs : Canonical s) (r : Fin 22) :
    poseidon2.apply_round_by_index s (Usize.ofNatCore r.val (by have := r.isLt;scalar_tac)) =
      (do let out ← R0PoseidonCopy.apply_round s (Usize.ofNatCore r.val (by have := r.isLt;scalar_tac)); ok (some (),out)) := by
  fin_cases r
  · exact copy00 s hs
  · exact copy01 s hs
  · exact copy02 s hs
  · exact copy03 s hs
  · exact copy04 s hs
  · exact copy05 s hs
  · exact copy06 s hs
  · exact copy07 s hs
  · exact copy08 s hs
  · exact copy09 s hs
  · exact copy10 s hs
  · exact copy11 s hs
  · exact copy12 s hs
  · exact copy13 s hs
  · exact copy14 s hs
  · exact copy15 s hs
  · exact copy16 s hs
  · exact copy17 s hs
  · exact copy18 s hs
  · exact copy19 s hs
  · exact copy20 s hs
  · exact copy21 s hs
#print axioms source
end R1Z.PV_RunJoin_IndexedCopy19
