/- Namespace port of BuilderPrimitiveDigests: same symbolic proof, actual forest extraction. -/
import R1Z.PV_Src_Forest_InverseResult

/-! Symbolic identities for duplicate primitive extractions. Every recursive
identity uses a decreasing suffix bound; no concrete cell is evaluated. -/
set_option autoImplicit false
namespace R1Z.PV_Src_Forest_PrimitiveDigests
open Aeneas Aeneas.Std Result R0Z.WriterRefine
open BuilderForestAdmissionPort

theorem block_P  :
    aspis_r0_block_writer_copies.P  = R0BlockCopies.P  := by
  simp only [aspis_r0_block_writer_copies.P,R0BlockCopies.P]

theorem block_TWEAK  :
    aspis_r0_block_writer_copies.TWEAK  = R0BlockCopies.TWEAK  := by
  simp only [aspis_r0_block_writer_copies.TWEAK,R0BlockCopies.TWEAK,block_P]

theorem block_m31_add (a : Std.U32) (b : Std.U32) :
    aspis_r0_block_writer_copies.m31_add a b = R0BlockCopies.m31_add a b := by
  simp only [aspis_r0_block_writer_copies.m31_add,R0BlockCopies.m31_add,block_P,block_TWEAK]

theorem block_write_block_rounds_loop0_loop0 (rounds : Array (Array Std.U32 16#usize) 11#usize) (block : Array Std.U32 256#usize) (r : Std.Usize) (lane : Std.Usize) :
    aspis_r0_block_writer_copies.write_block_rounds_loop0_loop0 rounds block r lane = R0BlockCopies.write_block_rounds_loop0_loop0 rounds block r lane := by
  generalize he : 16-lane.val = remaining
  induction remaining using Nat.strong_induction_on generalizing rounds block r lane with
  | h remaining ih =>
    rw [aspis_r0_block_writer_copies.write_block_rounds_loop0_loop0,R0BlockCopies.write_block_rounds_loop0_loop0]
    by_cases hit : lane.val < 16
    · have ht : lane < 16#usize := by simpa [UScalar.lt_equiv] using hit
      have hn : (Usize.wrapping_add lane 1#usize).val = lane.val+1 := by
        rw [uadd _ _ (by simp; omega)]; rfl
      have hnext : ∀ (rounds : Array (Array Std.U32 16#usize) 11#usize) (block : Array Std.U32 256#usize) (r : Std.Usize),
          aspis_r0_block_writer_copies.write_block_rounds_loop0_loop0 rounds block r (Usize.wrapping_add lane 1#usize) = R0BlockCopies.write_block_rounds_loop0_loop0 rounds block r (Usize.wrapping_add lane 1#usize) := by
        intros rounds block r
        exact ih (16-(Usize.wrapping_add lane 1#usize).val) (by omega) rounds block r (Usize.wrapping_add lane 1#usize) rfl
      simp only [if_pos ht,lift,bind_tc_ok,hnext,block_P,block_TWEAK,block_m31_add]
    · have ht : ¬lane < 16#usize := by simpa [UScalar.lt_equiv] using hit
      simp only [if_neg ht]

theorem block_write_block_rounds_loop0 (rounds : Array (Array Std.U32 16#usize) 11#usize) (block : Array Std.U32 256#usize) (r : Std.Usize) :
    aspis_r0_block_writer_copies.write_block_rounds_loop0 rounds block r = R0BlockCopies.write_block_rounds_loop0 rounds block r := by
  generalize he : 11-r.val = remaining
  induction remaining using Nat.strong_induction_on generalizing rounds block r with
  | h remaining ih =>
    rw [aspis_r0_block_writer_copies.write_block_rounds_loop0,R0BlockCopies.write_block_rounds_loop0]
    by_cases hit : r.val < 11
    · have ht : r < 11#usize := by simpa [UScalar.lt_equiv] using hit
      have hn : (Usize.wrapping_add r 1#usize).val = r.val+1 := by
        rw [uadd _ _ (by simp; omega)]; rfl
      have hnext : ∀ (rounds : Array (Array Std.U32 16#usize) 11#usize) (block : Array Std.U32 256#usize),
          aspis_r0_block_writer_copies.write_block_rounds_loop0 rounds block (Usize.wrapping_add r 1#usize) = R0BlockCopies.write_block_rounds_loop0 rounds block (Usize.wrapping_add r 1#usize) := by
        intros rounds block
        exact ih (11-(Usize.wrapping_add r 1#usize).val) (by omega) rounds block (Usize.wrapping_add r 1#usize) rfl
      simp only [if_pos ht,lift,bind_tc_ok,hnext,block_P,block_TWEAK,block_m31_add,block_write_block_rounds_loop0_loop0]
    · have ht : ¬r < 11#usize := by simpa [UScalar.lt_equiv] using hit
      simp only [if_neg ht]

theorem block_write_block_rounds (block : Array Std.U32 256#usize) (rounds : Array (Array Std.U32 16#usize) 11#usize) :
    aspis_r0_block_writer_copies.write_block_rounds block rounds = R0BlockCopies.write_block_rounds block rounds := by
  simp only [aspis_r0_block_writer_copies.write_block_rounds,R0BlockCopies.write_block_rounds,block_P,block_TWEAK,block_m31_add,block_write_block_rounds_loop0_loop0,block_write_block_rounds_loop0]

theorem block_write_block_ends_loop (pre : Array Std.U32 16#usize) (absorb : Array Std.U32 16#usize) (block : Array Std.U32 256#usize) (lane : Std.Usize) :
    aspis_r0_block_writer_copies.write_block_ends_loop pre absorb block lane = R0BlockCopies.write_block_ends_loop pre absorb block lane := by
  generalize he : 16-lane.val = remaining
  induction remaining using Nat.strong_induction_on generalizing pre absorb block lane with
  | h remaining ih =>
    rw [aspis_r0_block_writer_copies.write_block_ends_loop,R0BlockCopies.write_block_ends_loop]
    by_cases hit : lane.val < 16
    · have ht : lane < 16#usize := by simpa [UScalar.lt_equiv] using hit
      have hn : (Usize.wrapping_add lane 1#usize).val = lane.val+1 := by
        rw [uadd _ _ (by simp; omega)]; rfl
      have hnext : ∀ (pre : Array Std.U32 16#usize) (absorb : Array Std.U32 16#usize) (block : Array Std.U32 256#usize),
          aspis_r0_block_writer_copies.write_block_ends_loop pre absorb block (Usize.wrapping_add lane 1#usize) = R0BlockCopies.write_block_ends_loop pre absorb block (Usize.wrapping_add lane 1#usize) := by
        intros pre absorb block
        exact ih (16-(Usize.wrapping_add lane 1#usize).val) (by omega) pre absorb block (Usize.wrapping_add lane 1#usize) rfl
      simp only [if_pos ht,lift,bind_tc_ok,hnext,block_P,block_TWEAK,block_m31_add,block_write_block_rounds_loop0_loop0,block_write_block_rounds_loop0,block_write_block_rounds]
    · have ht : ¬lane < 16#usize := by simpa [UScalar.lt_equiv] using hit
      simp only [if_neg ht]

theorem block_write_block_ends (block : Array Std.U32 256#usize) (pre : Array Std.U32 16#usize) (absorb : Array Std.U32 16#usize) :
    aspis_r0_block_writer_copies.write_block_ends block pre absorb = R0BlockCopies.write_block_ends block pre absorb := by
  simp only [aspis_r0_block_writer_copies.write_block_ends,R0BlockCopies.write_block_ends,block_P,block_TWEAK,block_m31_add,block_write_block_rounds_loop0_loop0,block_write_block_rounds_loop0,block_write_block_rounds,block_write_block_ends_loop]

theorem block_write_block (pre : Array Std.U32 16#usize) (absorb : Array Std.U32 16#usize) (rounds : Array (Array Std.U32 16#usize) 11#usize) :
    aspis_r0_block_writer_copies.write_block pre absorb rounds = R0BlockCopies.write_block pre absorb rounds := by
  simp only [aspis_r0_block_writer_copies.write_block,R0BlockCopies.write_block,block_P,block_TWEAK,block_m31_add,block_write_block_rounds_loop0_loop0,block_write_block_rounds_loop0,block_write_block_rounds,block_write_block_ends_loop,block_write_block_ends]

theorem block_node_pre_loop (right : Array Std.U32 8#usize) (pre : Array Std.U32 16#usize) (lane : Std.Usize) :
    aspis_r0_block_writer_copies.node_pre_loop right pre lane = R0BlockCopies.node_pre_loop right pre lane := by
  generalize he : 8-lane.val = remaining
  induction remaining using Nat.strong_induction_on generalizing right pre lane with
  | h remaining ih =>
    rw [aspis_r0_block_writer_copies.node_pre_loop,R0BlockCopies.node_pre_loop]
    by_cases hit : lane.val < 8
    · have ht : lane < 8#usize := by simpa [UScalar.lt_equiv] using hit
      have hn : (Usize.wrapping_add lane 1#usize).val = lane.val+1 := by
        rw [uadd _ _ (by simp; omega)]; rfl
      have hnext : ∀ (right : Array Std.U32 8#usize) (pre : Array Std.U32 16#usize),
          aspis_r0_block_writer_copies.node_pre_loop right pre (Usize.wrapping_add lane 1#usize) = R0BlockCopies.node_pre_loop right pre (Usize.wrapping_add lane 1#usize) := by
        intros right pre
        exact ih (8-(Usize.wrapping_add lane 1#usize).val) (by omega) right pre (Usize.wrapping_add lane 1#usize) rfl
      simp only [if_pos ht,lift,bind_tc_ok,hnext,block_P,block_TWEAK,block_m31_add,block_write_block_rounds_loop0_loop0,block_write_block_rounds_loop0,block_write_block_rounds,block_write_block_ends_loop,block_write_block_ends,block_write_block]
    · have ht : ¬lane < 8#usize := by simpa [UScalar.lt_equiv] using hit
      simp only [if_neg ht]

theorem block_node_pre (right : Array Std.U32 8#usize) :
    aspis_r0_block_writer_copies.node_pre right = R0BlockCopies.node_pre right := by
  simp only [aspis_r0_block_writer_copies.node_pre,R0BlockCopies.node_pre,block_P,block_TWEAK,block_m31_add,block_write_block_rounds_loop0_loop0,block_write_block_rounds_loop0,block_write_block_rounds,block_write_block_ends_loop,block_write_block_ends,block_write_block,block_node_pre_loop]

theorem block_node_absorb_loop (left : Array Std.U32 8#usize) (absorb : Array Std.U32 16#usize) (lane : Std.Usize) :
    aspis_r0_block_writer_copies.node_absorb_loop left absorb lane = R0BlockCopies.node_absorb_loop left absorb lane := by
  generalize he : 8-lane.val = remaining
  induction remaining using Nat.strong_induction_on generalizing left absorb lane with
  | h remaining ih =>
    rw [aspis_r0_block_writer_copies.node_absorb_loop,R0BlockCopies.node_absorb_loop]
    by_cases hit : lane.val < 8
    · have ht : lane < 8#usize := by simpa [UScalar.lt_equiv] using hit
      have hn : (Usize.wrapping_add lane 1#usize).val = lane.val+1 := by
        rw [uadd _ _ (by simp; omega)]; rfl
      have hnext : ∀ (left : Array Std.U32 8#usize) (absorb : Array Std.U32 16#usize),
          aspis_r0_block_writer_copies.node_absorb_loop left absorb (Usize.wrapping_add lane 1#usize) = R0BlockCopies.node_absorb_loop left absorb (Usize.wrapping_add lane 1#usize) := by
        intros left absorb
        exact ih (8-(Usize.wrapping_add lane 1#usize).val) (by omega) left absorb (Usize.wrapping_add lane 1#usize) rfl
      simp only [if_pos ht,lift,bind_tc_ok,hnext,block_P,block_TWEAK,block_m31_add,block_write_block_rounds_loop0_loop0,block_write_block_rounds_loop0,block_write_block_rounds,block_write_block_ends_loop,block_write_block_ends,block_write_block,block_node_pre_loop,block_node_pre]
    · have ht : ¬lane < 8#usize := by simpa [UScalar.lt_equiv] using hit
      simp only [if_neg ht]

theorem block_node_absorb (left : Array Std.U32 8#usize) :
    aspis_r0_block_writer_copies.node_absorb left = R0BlockCopies.node_absorb left := by
  simp only [aspis_r0_block_writer_copies.node_absorb,R0BlockCopies.node_absorb,block_P,block_TWEAK,block_m31_add,block_write_block_rounds_loop0_loop0,block_write_block_rounds_loop0,block_write_block_rounds,block_write_block_ends_loop,block_write_block_ends,block_write_block,block_node_pre_loop,block_node_pre,block_node_absorb_loop]

theorem block_sponge_init (domain : Std.U32) (len : Std.U32) :
    aspis_r0_block_writer_copies.sponge_init domain len = R0BlockCopies.sponge_init domain len := by
  simp only [aspis_r0_block_writer_copies.sponge_init,R0BlockCopies.sponge_init,block_P,block_TWEAK,block_m31_add,block_write_block_rounds_loop0_loop0,block_write_block_rounds_loop0,block_write_block_rounds,block_write_block_ends_loop,block_write_block_ends,block_write_block,block_node_pre_loop,block_node_pre,block_node_absorb_loop,block_node_absorb]

theorem block_sponge_absorb_loop (chunk : Array Std.U32 8#usize) (len : Std.Usize) (absorb : Array Std.U32 16#usize) (lane : Std.Usize) :
    aspis_r0_block_writer_copies.sponge_absorb_loop chunk len absorb lane = R0BlockCopies.sponge_absorb_loop chunk len absorb lane := by
  generalize he : 8-lane.val = remaining
  induction remaining using Nat.strong_induction_on generalizing chunk len absorb lane with
  | h remaining ih =>
    rw [aspis_r0_block_writer_copies.sponge_absorb_loop,R0BlockCopies.sponge_absorb_loop]
    by_cases hit : lane.val < 8
    · have ht : lane < 8#usize := by simpa [UScalar.lt_equiv] using hit
      have hn : (Usize.wrapping_add lane 1#usize).val = lane.val+1 := by
        rw [uadd _ _ (by simp; omega)]; rfl
      have hnext : ∀ (chunk : Array Std.U32 8#usize) (len : Std.Usize) (absorb : Array Std.U32 16#usize),
          aspis_r0_block_writer_copies.sponge_absorb_loop chunk len absorb (Usize.wrapping_add lane 1#usize) = R0BlockCopies.sponge_absorb_loop chunk len absorb (Usize.wrapping_add lane 1#usize) := by
        intros chunk len absorb
        exact ih (8-(Usize.wrapping_add lane 1#usize).val) (by omega) chunk len absorb (Usize.wrapping_add lane 1#usize) rfl
      simp only [if_pos ht,lift,bind_tc_ok,hnext,block_P,block_TWEAK,block_m31_add,block_write_block_rounds_loop0_loop0,block_write_block_rounds_loop0,block_write_block_rounds,block_write_block_ends_loop,block_write_block_ends,block_write_block,block_node_pre_loop,block_node_pre,block_node_absorb_loop,block_node_absorb,block_sponge_init]
    · have ht : ¬lane < 8#usize := by simpa [UScalar.lt_equiv] using hit
      simp only [if_neg ht]

theorem block_sponge_absorb (chunk : Array Std.U32 8#usize) (len : Std.Usize) :
    aspis_r0_block_writer_copies.sponge_absorb chunk len = R0BlockCopies.sponge_absorb chunk len := by
  simp only [aspis_r0_block_writer_copies.sponge_absorb,R0BlockCopies.sponge_absorb,block_P,block_TWEAK,block_m31_add,block_write_block_rounds_loop0_loop0,block_write_block_rounds_loop0,block_write_block_rounds,block_write_block_ends_loop,block_write_block_ends,block_write_block,block_node_pre_loop,block_node_pre,block_node_absorb_loop,block_node_absorb,block_sponge_init,block_sponge_absorb_loop]

theorem poseidon_P  :
    aspis_r0_poseidon_copy.P  = R0PoseidonCopy.P  := by
  simp only [aspis_r0_poseidon_copy.P,R0PoseidonCopy.P,block_P,block_TWEAK,block_m31_add,block_write_block_rounds_loop0_loop0,block_write_block_rounds_loop0,block_write_block_rounds,block_write_block_ends_loop,block_write_block_ends,block_write_block,block_node_pre_loop,block_node_pre,block_node_absorb_loop,block_node_absorb,block_sponge_init,block_sponge_absorb_loop,block_sponge_absorb]

theorem poseidon_EXTERNAL_INITIAL  :
    aspis_r0_poseidon_copy.EXTERNAL_INITIAL  = R0PoseidonCopy.EXTERNAL_INITIAL  := by
  simp only [aspis_r0_poseidon_copy.EXTERNAL_INITIAL,R0PoseidonCopy.EXTERNAL_INITIAL,block_P,block_TWEAK,block_m31_add,block_write_block_rounds_loop0_loop0,block_write_block_rounds_loop0,block_write_block_rounds,block_write_block_ends_loop,block_write_block_ends,block_write_block,block_node_pre_loop,block_node_pre,block_node_absorb_loop,block_node_absorb,block_sponge_init,block_sponge_absorb_loop,block_sponge_absorb,poseidon_P]

theorem poseidon_EXTERNAL_FINAL  :
    aspis_r0_poseidon_copy.EXTERNAL_FINAL  = R0PoseidonCopy.EXTERNAL_FINAL  := by
  simp only [aspis_r0_poseidon_copy.EXTERNAL_FINAL,R0PoseidonCopy.EXTERNAL_FINAL,block_P,block_TWEAK,block_m31_add,block_write_block_rounds_loop0_loop0,block_write_block_rounds_loop0,block_write_block_rounds,block_write_block_ends_loop,block_write_block_ends,block_write_block,block_node_pre_loop,block_node_pre,block_node_absorb_loop,block_node_absorb,block_sponge_init,block_sponge_absorb_loop,block_sponge_absorb,poseidon_P,poseidon_EXTERNAL_INITIAL]

theorem poseidon_INTERNAL  :
    aspis_r0_poseidon_copy.INTERNAL  = R0PoseidonCopy.INTERNAL  := by
  simp only [aspis_r0_poseidon_copy.INTERNAL,R0PoseidonCopy.INTERNAL,block_P,block_TWEAK,block_m31_add,block_write_block_rounds_loop0_loop0,block_write_block_rounds_loop0,block_write_block_rounds,block_write_block_ends_loop,block_write_block_ends,block_write_block,block_node_pre_loop,block_node_pre,block_node_absorb_loop,block_node_absorb,block_sponge_init,block_sponge_absorb_loop,block_sponge_absorb,poseidon_P,poseidon_EXTERNAL_INITIAL,poseidon_EXTERNAL_FINAL]

theorem poseidon_INTERNAL_SHIFTS  :
    aspis_r0_poseidon_copy.INTERNAL_SHIFTS  = R0PoseidonCopy.INTERNAL_SHIFTS  := by
  simp only [aspis_r0_poseidon_copy.INTERNAL_SHIFTS,R0PoseidonCopy.INTERNAL_SHIFTS,block_P,block_TWEAK,block_m31_add,block_write_block_rounds_loop0_loop0,block_write_block_rounds_loop0,block_write_block_rounds,block_write_block_ends_loop,block_write_block_ends,block_write_block,block_node_pre_loop,block_node_pre,block_node_absorb_loop,block_node_absorb,block_sponge_init,block_sponge_absorb_loop,block_sponge_absorb,poseidon_P,poseidon_EXTERNAL_INITIAL,poseidon_EXTERNAL_FINAL,poseidon_INTERNAL]

theorem poseidon_m31_add (a : Std.U32) (b : Std.U32) :
    aspis_r0_poseidon_copy.m31_add a b = R0PoseidonCopy.m31_add a b := by
  simp only [aspis_r0_poseidon_copy.m31_add,R0PoseidonCopy.m31_add,block_P,block_TWEAK,block_m31_add,block_write_block_rounds_loop0_loop0,block_write_block_rounds_loop0,block_write_block_rounds,block_write_block_ends_loop,block_write_block_ends,block_write_block,block_node_pre_loop,block_node_pre,block_node_absorb_loop,block_node_absorb,block_sponge_init,block_sponge_absorb_loop,block_sponge_absorb,poseidon_P,poseidon_EXTERNAL_INITIAL,poseidon_EXTERNAL_FINAL,poseidon_INTERNAL,poseidon_INTERNAL_SHIFTS]

theorem poseidon_m31_mul (a : Std.U32) (b : Std.U32) :
    aspis_r0_poseidon_copy.m31_mul a b = R0PoseidonCopy.m31_mul a b := by
  simp only [aspis_r0_poseidon_copy.m31_mul,R0PoseidonCopy.m31_mul,block_P,block_TWEAK,block_m31_add,block_write_block_rounds_loop0_loop0,block_write_block_rounds_loop0,block_write_block_rounds,block_write_block_ends_loop,block_write_block_ends,block_write_block,block_node_pre_loop,block_node_pre,block_node_absorb_loop,block_node_absorb,block_sponge_init,block_sponge_absorb_loop,block_sponge_absorb,poseidon_P,poseidon_EXTERNAL_INITIAL,poseidon_EXTERNAL_FINAL,poseidon_INTERNAL,poseidon_INTERNAL_SHIFTS,poseidon_m31_add]

theorem poseidon_pow5 (x : Std.U32) :
    aspis_r0_poseidon_copy.pow5 x = R0PoseidonCopy.pow5 x := by
  simp only [aspis_r0_poseidon_copy.pow5,R0PoseidonCopy.pow5,block_P,block_TWEAK,block_m31_add,block_write_block_rounds_loop0_loop0,block_write_block_rounds_loop0,block_write_block_rounds,block_write_block_ends_loop,block_write_block_ends,block_write_block,block_node_pre_loop,block_node_pre,block_node_absorb_loop,block_node_absorb,block_sponge_init,block_sponge_absorb_loop,block_sponge_absorb,poseidon_P,poseidon_EXTERNAL_INITIAL,poseidon_EXTERNAL_FINAL,poseidon_INTERNAL,poseidon_INTERNAL_SHIFTS,poseidon_m31_add,poseidon_m31_mul]

theorem poseidon_mat4 (a : Std.U32) (b : Std.U32) (c : Std.U32) (d : Std.U32) :
    aspis_r0_poseidon_copy.mat4 a b c d = R0PoseidonCopy.mat4 a b c d := by
  simp only [aspis_r0_poseidon_copy.mat4,R0PoseidonCopy.mat4,block_P,block_TWEAK,block_m31_add,block_write_block_rounds_loop0_loop0,block_write_block_rounds_loop0,block_write_block_rounds,block_write_block_ends_loop,block_write_block_ends,block_write_block,block_node_pre_loop,block_node_pre,block_node_absorb_loop,block_node_absorb,block_sponge_init,block_sponge_absorb_loop,block_sponge_absorb,poseidon_P,poseidon_EXTERNAL_INITIAL,poseidon_EXTERNAL_FINAL,poseidon_INTERNAL,poseidon_INTERNAL_SHIFTS,poseidon_m31_add,poseidon_m31_mul,poseidon_pow5]

theorem poseidon_ext_groups_loop (state : Array Std.U32 16#usize) (out : Array Std.U32 16#usize) (g : Std.Usize) :
    aspis_r0_poseidon_copy.ext_groups_loop state out g = R0PoseidonCopy.ext_groups_loop state out g := by
  generalize he : 4-g.val = remaining
  induction remaining using Nat.strong_induction_on generalizing state out g with
  | h remaining ih =>
    rw [aspis_r0_poseidon_copy.ext_groups_loop,R0PoseidonCopy.ext_groups_loop]
    by_cases hit : g.val < 4
    · have ht : g < 4#usize := by simpa [UScalar.lt_equiv] using hit
      have hn : (Usize.wrapping_add g 1#usize).val = g.val+1 := by
        rw [uadd _ _ (by simp; omega)]; rfl
      have hnext : ∀ (state : Array Std.U32 16#usize) (out : Array Std.U32 16#usize),
          aspis_r0_poseidon_copy.ext_groups_loop state out (Usize.wrapping_add g 1#usize) = R0PoseidonCopy.ext_groups_loop state out (Usize.wrapping_add g 1#usize) := by
        intros state out
        exact ih (4-(Usize.wrapping_add g 1#usize).val) (by omega) state out (Usize.wrapping_add g 1#usize) rfl
      simp only [if_pos ht,lift,bind_tc_ok,hnext,block_P,block_TWEAK,block_m31_add,block_write_block_rounds_loop0_loop0,block_write_block_rounds_loop0,block_write_block_rounds,block_write_block_ends_loop,block_write_block_ends,block_write_block,block_node_pre_loop,block_node_pre,block_node_absorb_loop,block_node_absorb,block_sponge_init,block_sponge_absorb_loop,block_sponge_absorb,poseidon_P,poseidon_EXTERNAL_INITIAL,poseidon_EXTERNAL_FINAL,poseidon_INTERNAL,poseidon_INTERNAL_SHIFTS,poseidon_m31_add,poseidon_m31_mul,poseidon_pow5,poseidon_mat4]
    · have ht : ¬g < 4#usize := by simpa [UScalar.lt_equiv] using hit
      simp only [if_neg ht]

theorem poseidon_ext_groups (state : Array Std.U32 16#usize) :
    aspis_r0_poseidon_copy.ext_groups state = R0PoseidonCopy.ext_groups state := by
  simp only [aspis_r0_poseidon_copy.ext_groups,R0PoseidonCopy.ext_groups,block_P,block_TWEAK,block_m31_add,block_write_block_rounds_loop0_loop0,block_write_block_rounds_loop0,block_write_block_rounds,block_write_block_ends_loop,block_write_block_ends,block_write_block,block_node_pre_loop,block_node_pre,block_node_absorb_loop,block_node_absorb,block_sponge_init,block_sponge_absorb_loop,block_sponge_absorb,poseidon_P,poseidon_EXTERNAL_INITIAL,poseidon_EXTERNAL_FINAL,poseidon_INTERNAL,poseidon_INTERNAL_SHIFTS,poseidon_m31_add,poseidon_m31_mul,poseidon_pow5,poseidon_mat4,poseidon_ext_groups_loop]

theorem poseidon_ext_sums_loop (grouped : Array Std.U32 16#usize) (sums : Array Std.U32 4#usize) (col : Std.Usize) :
    aspis_r0_poseidon_copy.ext_sums_loop grouped sums col = R0PoseidonCopy.ext_sums_loop grouped sums col := by
  generalize he : 4-col.val = remaining
  induction remaining using Nat.strong_induction_on generalizing grouped sums col with
  | h remaining ih =>
    rw [aspis_r0_poseidon_copy.ext_sums_loop,R0PoseidonCopy.ext_sums_loop]
    by_cases hit : col.val < 4
    · have ht : col < 4#usize := by simpa [UScalar.lt_equiv] using hit
      have hn : (Usize.wrapping_add col 1#usize).val = col.val+1 := by
        rw [uadd _ _ (by simp; omega)]; rfl
      have hnext : ∀ (grouped : Array Std.U32 16#usize) (sums : Array Std.U32 4#usize),
          aspis_r0_poseidon_copy.ext_sums_loop grouped sums (Usize.wrapping_add col 1#usize) = R0PoseidonCopy.ext_sums_loop grouped sums (Usize.wrapping_add col 1#usize) := by
        intros grouped sums
        exact ih (4-(Usize.wrapping_add col 1#usize).val) (by omega) grouped sums (Usize.wrapping_add col 1#usize) rfl
      simp only [if_pos ht,lift,bind_tc_ok,hnext,block_P,block_TWEAK,block_m31_add,block_write_block_rounds_loop0_loop0,block_write_block_rounds_loop0,block_write_block_rounds,block_write_block_ends_loop,block_write_block_ends,block_write_block,block_node_pre_loop,block_node_pre,block_node_absorb_loop,block_node_absorb,block_sponge_init,block_sponge_absorb_loop,block_sponge_absorb,poseidon_P,poseidon_EXTERNAL_INITIAL,poseidon_EXTERNAL_FINAL,poseidon_INTERNAL,poseidon_INTERNAL_SHIFTS,poseidon_m31_add,poseidon_m31_mul,poseidon_pow5,poseidon_mat4,poseidon_ext_groups_loop,poseidon_ext_groups]
    · have ht : ¬col < 4#usize := by simpa [UScalar.lt_equiv] using hit
      simp only [if_neg ht]

theorem poseidon_ext_sums (grouped : Array Std.U32 16#usize) :
    aspis_r0_poseidon_copy.ext_sums grouped = R0PoseidonCopy.ext_sums grouped := by
  simp only [aspis_r0_poseidon_copy.ext_sums,R0PoseidonCopy.ext_sums,block_P,block_TWEAK,block_m31_add,block_write_block_rounds_loop0_loop0,block_write_block_rounds_loop0,block_write_block_rounds,block_write_block_ends_loop,block_write_block_ends,block_write_block,block_node_pre_loop,block_node_pre,block_node_absorb_loop,block_node_absorb,block_sponge_init,block_sponge_absorb_loop,block_sponge_absorb,poseidon_P,poseidon_EXTERNAL_INITIAL,poseidon_EXTERNAL_FINAL,poseidon_INTERNAL,poseidon_INTERNAL_SHIFTS,poseidon_m31_add,poseidon_m31_mul,poseidon_pow5,poseidon_mat4,poseidon_ext_groups_loop,poseidon_ext_groups,poseidon_ext_sums_loop]

theorem poseidon_ext_add_loop (grouped : Array Std.U32 16#usize) (sums : Array Std.U32 4#usize) (out : Array Std.U32 16#usize) (i : Std.Usize) :
    aspis_r0_poseidon_copy.ext_add_loop grouped sums out i = R0PoseidonCopy.ext_add_loop grouped sums out i := by
  generalize he : 16-i.val = remaining
  induction remaining using Nat.strong_induction_on generalizing grouped sums out i with
  | h remaining ih =>
    rw [aspis_r0_poseidon_copy.ext_add_loop,R0PoseidonCopy.ext_add_loop]
    by_cases hit : i.val < 16
    · have ht : i < 16#usize := by simpa [UScalar.lt_equiv] using hit
      have hn : (Usize.wrapping_add i 1#usize).val = i.val+1 := by
        rw [uadd _ _ (by simp; omega)]; rfl
      have hnext : ∀ (grouped : Array Std.U32 16#usize) (sums : Array Std.U32 4#usize) (out : Array Std.U32 16#usize),
          aspis_r0_poseidon_copy.ext_add_loop grouped sums out (Usize.wrapping_add i 1#usize) = R0PoseidonCopy.ext_add_loop grouped sums out (Usize.wrapping_add i 1#usize) := by
        intros grouped sums out
        exact ih (16-(Usize.wrapping_add i 1#usize).val) (by omega) grouped sums out (Usize.wrapping_add i 1#usize) rfl
      simp only [if_pos ht,lift,bind_tc_ok,hnext,block_P,block_TWEAK,block_m31_add,block_write_block_rounds_loop0_loop0,block_write_block_rounds_loop0,block_write_block_rounds,block_write_block_ends_loop,block_write_block_ends,block_write_block,block_node_pre_loop,block_node_pre,block_node_absorb_loop,block_node_absorb,block_sponge_init,block_sponge_absorb_loop,block_sponge_absorb,poseidon_P,poseidon_EXTERNAL_INITIAL,poseidon_EXTERNAL_FINAL,poseidon_INTERNAL,poseidon_INTERNAL_SHIFTS,poseidon_m31_add,poseidon_m31_mul,poseidon_pow5,poseidon_mat4,poseidon_ext_groups_loop,poseidon_ext_groups,poseidon_ext_sums_loop,poseidon_ext_sums]
    · have ht : ¬i < 16#usize := by simpa [UScalar.lt_equiv] using hit
      simp only [if_neg ht]

theorem poseidon_ext_add (grouped : Array Std.U32 16#usize) (sums : Array Std.U32 4#usize) :
    aspis_r0_poseidon_copy.ext_add grouped sums = R0PoseidonCopy.ext_add grouped sums := by
  simp only [aspis_r0_poseidon_copy.ext_add,R0PoseidonCopy.ext_add,block_P,block_TWEAK,block_m31_add,block_write_block_rounds_loop0_loop0,block_write_block_rounds_loop0,block_write_block_rounds,block_write_block_ends_loop,block_write_block_ends,block_write_block,block_node_pre_loop,block_node_pre,block_node_absorb_loop,block_node_absorb,block_sponge_init,block_sponge_absorb_loop,block_sponge_absorb,poseidon_P,poseidon_EXTERNAL_INITIAL,poseidon_EXTERNAL_FINAL,poseidon_INTERNAL,poseidon_INTERNAL_SHIFTS,poseidon_m31_add,poseidon_m31_mul,poseidon_pow5,poseidon_mat4,poseidon_ext_groups_loop,poseidon_ext_groups,poseidon_ext_sums_loop,poseidon_ext_sums,poseidon_ext_add_loop]

theorem poseidon_external_linear (state : Array Std.U32 16#usize) :
    aspis_r0_poseidon_copy.external_linear state = R0PoseidonCopy.external_linear state := by
  simp only [aspis_r0_poseidon_copy.external_linear,R0PoseidonCopy.external_linear,block_P,block_TWEAK,block_m31_add,block_write_block_rounds_loop0_loop0,block_write_block_rounds_loop0,block_write_block_rounds,block_write_block_ends_loop,block_write_block_ends,block_write_block,block_node_pre_loop,block_node_pre,block_node_absorb_loop,block_node_absorb,block_sponge_init,block_sponge_absorb_loop,block_sponge_absorb,poseidon_P,poseidon_EXTERNAL_INITIAL,poseidon_EXTERNAL_FINAL,poseidon_INTERNAL,poseidon_INTERNAL_SHIFTS,poseidon_m31_add,poseidon_m31_mul,poseidon_pow5,poseidon_mat4,poseidon_ext_groups_loop,poseidon_ext_groups,poseidon_ext_sums_loop,poseidon_ext_sums,poseidon_ext_add_loop,poseidon_ext_add]

theorem poseidon_int_part_sum_loop (state : Array Std.U32 16#usize) (acc : Std.U64) (i : Std.Usize) :
    aspis_r0_poseidon_copy.int_part_sum_loop state acc i = R0PoseidonCopy.int_part_sum_loop state acc i := by
  generalize he : 16-i.val = remaining
  induction remaining using Nat.strong_induction_on generalizing state acc i with
  | h remaining ih =>
    rw [aspis_r0_poseidon_copy.int_part_sum_loop,R0PoseidonCopy.int_part_sum_loop]
    by_cases hit : i.val < 16
    · have ht : i < 16#usize := by simpa [UScalar.lt_equiv] using hit
      have hn : (Usize.wrapping_add i 1#usize).val = i.val+1 := by
        rw [uadd _ _ (by simp; omega)]; rfl
      have hnext : ∀ (state : Array Std.U32 16#usize) (acc : Std.U64),
          aspis_r0_poseidon_copy.int_part_sum_loop state acc (Usize.wrapping_add i 1#usize) = R0PoseidonCopy.int_part_sum_loop state acc (Usize.wrapping_add i 1#usize) := by
        intros state acc
        exact ih (16-(Usize.wrapping_add i 1#usize).val) (by omega) state acc (Usize.wrapping_add i 1#usize) rfl
      simp only [if_pos ht,lift,bind_tc_ok,hnext,block_P,block_TWEAK,block_m31_add,block_write_block_rounds_loop0_loop0,block_write_block_rounds_loop0,block_write_block_rounds,block_write_block_ends_loop,block_write_block_ends,block_write_block,block_node_pre_loop,block_node_pre,block_node_absorb_loop,block_node_absorb,block_sponge_init,block_sponge_absorb_loop,block_sponge_absorb,poseidon_P,poseidon_EXTERNAL_INITIAL,poseidon_EXTERNAL_FINAL,poseidon_INTERNAL,poseidon_INTERNAL_SHIFTS,poseidon_m31_add,poseidon_m31_mul,poseidon_pow5,poseidon_mat4,poseidon_ext_groups_loop,poseidon_ext_groups,poseidon_ext_sums_loop,poseidon_ext_sums,poseidon_ext_add_loop,poseidon_ext_add,poseidon_external_linear]
    · have ht : ¬i < 16#usize := by simpa [UScalar.lt_equiv] using hit
      simp only [if_neg ht]

theorem poseidon_int_part_sum (state : Array Std.U32 16#usize) :
    aspis_r0_poseidon_copy.int_part_sum state = R0PoseidonCopy.int_part_sum state := by
  simp only [aspis_r0_poseidon_copy.int_part_sum,R0PoseidonCopy.int_part_sum,block_P,block_TWEAK,block_m31_add,block_write_block_rounds_loop0_loop0,block_write_block_rounds_loop0,block_write_block_rounds,block_write_block_ends_loop,block_write_block_ends,block_write_block,block_node_pre_loop,block_node_pre,block_node_absorb_loop,block_node_absorb,block_sponge_init,block_sponge_absorb_loop,block_sponge_absorb,poseidon_P,poseidon_EXTERNAL_INITIAL,poseidon_EXTERNAL_FINAL,poseidon_INTERNAL,poseidon_INTERNAL_SHIFTS,poseidon_m31_add,poseidon_m31_mul,poseidon_pow5,poseidon_mat4,poseidon_ext_groups_loop,poseidon_ext_groups,poseidon_ext_sums_loop,poseidon_ext_sums,poseidon_ext_add_loop,poseidon_ext_add,poseidon_external_linear,poseidon_int_part_sum_loop]

theorem poseidon_internal_linear_loop (state : Array Std.U32 16#usize) (shifts : Array Std.U32 15#usize) (full : Std.U32) (out : Array Std.U32 16#usize) (i : Std.Usize) :
    aspis_r0_poseidon_copy.internal_linear_loop state shifts full out i = R0PoseidonCopy.internal_linear_loop state shifts full out i := by
  generalize he : 16-i.val = remaining
  induction remaining using Nat.strong_induction_on generalizing state shifts full out i with
  | h remaining ih =>
    rw [aspis_r0_poseidon_copy.internal_linear_loop,R0PoseidonCopy.internal_linear_loop]
    by_cases hit : i.val < 16
    · have ht : i < 16#usize := by simpa [UScalar.lt_equiv] using hit
      have hn : (Usize.wrapping_add i 1#usize).val = i.val+1 := by
        rw [uadd _ _ (by simp; omega)]; rfl
      have hnext : ∀ (state : Array Std.U32 16#usize) (shifts : Array Std.U32 15#usize) (full : Std.U32) (out : Array Std.U32 16#usize),
          aspis_r0_poseidon_copy.internal_linear_loop state shifts full out (Usize.wrapping_add i 1#usize) = R0PoseidonCopy.internal_linear_loop state shifts full out (Usize.wrapping_add i 1#usize) := by
        intros state shifts full out
        exact ih (16-(Usize.wrapping_add i 1#usize).val) (by omega) state shifts full out (Usize.wrapping_add i 1#usize) rfl
      simp only [if_pos ht,lift,bind_tc_ok,hnext,block_P,block_TWEAK,block_m31_add,block_write_block_rounds_loop0_loop0,block_write_block_rounds_loop0,block_write_block_rounds,block_write_block_ends_loop,block_write_block_ends,block_write_block,block_node_pre_loop,block_node_pre,block_node_absorb_loop,block_node_absorb,block_sponge_init,block_sponge_absorb_loop,block_sponge_absorb,poseidon_P,poseidon_EXTERNAL_INITIAL,poseidon_EXTERNAL_FINAL,poseidon_INTERNAL,poseidon_INTERNAL_SHIFTS,poseidon_m31_add,poseidon_m31_mul,poseidon_pow5,poseidon_mat4,poseidon_ext_groups_loop,poseidon_ext_groups,poseidon_ext_sums_loop,poseidon_ext_sums,poseidon_ext_add_loop,poseidon_ext_add,poseidon_external_linear,poseidon_int_part_sum_loop,poseidon_int_part_sum]
    · have ht : ¬i < 16#usize := by simpa [UScalar.lt_equiv] using hit
      simp only [if_neg ht]

theorem poseidon_internal_linear (state : Array Std.U32 16#usize) (shifts : Array Std.U32 15#usize) :
    aspis_r0_poseidon_copy.internal_linear state shifts = R0PoseidonCopy.internal_linear state shifts := by
  simp only [aspis_r0_poseidon_copy.internal_linear,R0PoseidonCopy.internal_linear,block_P,block_TWEAK,block_m31_add,block_write_block_rounds_loop0_loop0,block_write_block_rounds_loop0,block_write_block_rounds,block_write_block_ends_loop,block_write_block_ends,block_write_block,block_node_pre_loop,block_node_pre,block_node_absorb_loop,block_node_absorb,block_sponge_init,block_sponge_absorb_loop,block_sponge_absorb,poseidon_P,poseidon_EXTERNAL_INITIAL,poseidon_EXTERNAL_FINAL,poseidon_INTERNAL,poseidon_INTERNAL_SHIFTS,poseidon_m31_add,poseidon_m31_mul,poseidon_pow5,poseidon_mat4,poseidon_ext_groups_loop,poseidon_ext_groups,poseidon_ext_sums_loop,poseidon_ext_sums,poseidon_ext_add_loop,poseidon_ext_add,poseidon_external_linear,poseidon_int_part_sum_loop,poseidon_int_part_sum,poseidon_internal_linear_loop]

theorem poseidon_sbox_full_loop (state : Array Std.U32 16#usize) (c : Array Std.U32 16#usize) (out : Array Std.U32 16#usize) (i : Std.Usize) :
    aspis_r0_poseidon_copy.sbox_full_loop state c out i = R0PoseidonCopy.sbox_full_loop state c out i := by
  generalize he : 16-i.val = remaining
  induction remaining using Nat.strong_induction_on generalizing state c out i with
  | h remaining ih =>
    rw [aspis_r0_poseidon_copy.sbox_full_loop,R0PoseidonCopy.sbox_full_loop]
    by_cases hit : i.val < 16
    · have ht : i < 16#usize := by simpa [UScalar.lt_equiv] using hit
      have hn : (Usize.wrapping_add i 1#usize).val = i.val+1 := by
        rw [uadd _ _ (by simp; omega)]; rfl
      have hnext : ∀ (state : Array Std.U32 16#usize) (c : Array Std.U32 16#usize) (out : Array Std.U32 16#usize),
          aspis_r0_poseidon_copy.sbox_full_loop state c out (Usize.wrapping_add i 1#usize) = R0PoseidonCopy.sbox_full_loop state c out (Usize.wrapping_add i 1#usize) := by
        intros state c out
        exact ih (16-(Usize.wrapping_add i 1#usize).val) (by omega) state c out (Usize.wrapping_add i 1#usize) rfl
      simp only [if_pos ht,lift,bind_tc_ok,hnext,block_P,block_TWEAK,block_m31_add,block_write_block_rounds_loop0_loop0,block_write_block_rounds_loop0,block_write_block_rounds,block_write_block_ends_loop,block_write_block_ends,block_write_block,block_node_pre_loop,block_node_pre,block_node_absorb_loop,block_node_absorb,block_sponge_init,block_sponge_absorb_loop,block_sponge_absorb,poseidon_P,poseidon_EXTERNAL_INITIAL,poseidon_EXTERNAL_FINAL,poseidon_INTERNAL,poseidon_INTERNAL_SHIFTS,poseidon_m31_add,poseidon_m31_mul,poseidon_pow5,poseidon_mat4,poseidon_ext_groups_loop,poseidon_ext_groups,poseidon_ext_sums_loop,poseidon_ext_sums,poseidon_ext_add_loop,poseidon_ext_add,poseidon_external_linear,poseidon_int_part_sum_loop,poseidon_int_part_sum,poseidon_internal_linear_loop,poseidon_internal_linear]
    · have ht : ¬i < 16#usize := by simpa [UScalar.lt_equiv] using hit
      simp only [if_neg ht]

theorem poseidon_sbox_full (state : Array Std.U32 16#usize) (c : Array Std.U32 16#usize) :
    aspis_r0_poseidon_copy.sbox_full state c = R0PoseidonCopy.sbox_full state c := by
  simp only [aspis_r0_poseidon_copy.sbox_full,R0PoseidonCopy.sbox_full,block_P,block_TWEAK,block_m31_add,block_write_block_rounds_loop0_loop0,block_write_block_rounds_loop0,block_write_block_rounds,block_write_block_ends_loop,block_write_block_ends,block_write_block,block_node_pre_loop,block_node_pre,block_node_absorb_loop,block_node_absorb,block_sponge_init,block_sponge_absorb_loop,block_sponge_absorb,poseidon_P,poseidon_EXTERNAL_INITIAL,poseidon_EXTERNAL_FINAL,poseidon_INTERNAL,poseidon_INTERNAL_SHIFTS,poseidon_m31_add,poseidon_m31_mul,poseidon_pow5,poseidon_mat4,poseidon_ext_groups_loop,poseidon_ext_groups,poseidon_ext_sums_loop,poseidon_ext_sums,poseidon_ext_add_loop,poseidon_ext_add,poseidon_external_linear,poseidon_int_part_sum_loop,poseidon_int_part_sum,poseidon_internal_linear_loop,poseidon_internal_linear,poseidon_sbox_full_loop]

theorem poseidon_full_round (state : Array Std.U32 16#usize) (c : Array Std.U32 16#usize) :
    aspis_r0_poseidon_copy.full_round state c = R0PoseidonCopy.full_round state c := by
  simp only [aspis_r0_poseidon_copy.full_round,R0PoseidonCopy.full_round,block_P,block_TWEAK,block_m31_add,block_write_block_rounds_loop0_loop0,block_write_block_rounds_loop0,block_write_block_rounds,block_write_block_ends_loop,block_write_block_ends,block_write_block,block_node_pre_loop,block_node_pre,block_node_absorb_loop,block_node_absorb,block_sponge_init,block_sponge_absorb_loop,block_sponge_absorb,poseidon_P,poseidon_EXTERNAL_INITIAL,poseidon_EXTERNAL_FINAL,poseidon_INTERNAL,poseidon_INTERNAL_SHIFTS,poseidon_m31_add,poseidon_m31_mul,poseidon_pow5,poseidon_mat4,poseidon_ext_groups_loop,poseidon_ext_groups,poseidon_ext_sums_loop,poseidon_ext_sums,poseidon_ext_add_loop,poseidon_ext_add,poseidon_external_linear,poseidon_int_part_sum_loop,poseidon_int_part_sum,poseidon_internal_linear_loop,poseidon_internal_linear,poseidon_sbox_full_loop,poseidon_sbox_full]

theorem poseidon_internal_round (state : Array Std.U32 16#usize) (c0 : Std.U32) (shifts : Array Std.U32 15#usize) :
    aspis_r0_poseidon_copy.internal_round state c0 shifts = R0PoseidonCopy.internal_round state c0 shifts := by
  simp only [aspis_r0_poseidon_copy.internal_round,R0PoseidonCopy.internal_round,block_P,block_TWEAK,block_m31_add,block_write_block_rounds_loop0_loop0,block_write_block_rounds_loop0,block_write_block_rounds,block_write_block_ends_loop,block_write_block_ends,block_write_block,block_node_pre_loop,block_node_pre,block_node_absorb_loop,block_node_absorb,block_sponge_init,block_sponge_absorb_loop,block_sponge_absorb,poseidon_P,poseidon_EXTERNAL_INITIAL,poseidon_EXTERNAL_FINAL,poseidon_INTERNAL,poseidon_INTERNAL_SHIFTS,poseidon_m31_add,poseidon_m31_mul,poseidon_pow5,poseidon_mat4,poseidon_ext_groups_loop,poseidon_ext_groups,poseidon_ext_sums_loop,poseidon_ext_sums,poseidon_ext_add_loop,poseidon_ext_add,poseidon_external_linear,poseidon_int_part_sum_loop,poseidon_int_part_sum,poseidon_internal_linear_loop,poseidon_internal_linear,poseidon_sbox_full_loop,poseidon_sbox_full,poseidon_full_round]

theorem poseidon_absorb_into_loop (pre : Array Std.U32 16#usize) (absorb : Array Std.U32 16#usize) (out : Array Std.U32 16#usize) (i : Std.Usize) :
    aspis_r0_poseidon_copy.absorb_into_loop pre absorb out i = R0PoseidonCopy.absorb_into_loop pre absorb out i := by
  generalize he : 8-i.val = remaining
  induction remaining using Nat.strong_induction_on generalizing pre absorb out i with
  | h remaining ih =>
    rw [aspis_r0_poseidon_copy.absorb_into_loop,R0PoseidonCopy.absorb_into_loop]
    by_cases hit : i.val < 8
    · have ht : i < 8#usize := by simpa [UScalar.lt_equiv] using hit
      have hn : (Usize.wrapping_add i 1#usize).val = i.val+1 := by
        rw [uadd _ _ (by simp; omega)]; rfl
      have hnext : ∀ (pre : Array Std.U32 16#usize) (absorb : Array Std.U32 16#usize) (out : Array Std.U32 16#usize),
          aspis_r0_poseidon_copy.absorb_into_loop pre absorb out (Usize.wrapping_add i 1#usize) = R0PoseidonCopy.absorb_into_loop pre absorb out (Usize.wrapping_add i 1#usize) := by
        intros pre absorb out
        exact ih (8-(Usize.wrapping_add i 1#usize).val) (by omega) pre absorb out (Usize.wrapping_add i 1#usize) rfl
      simp only [if_pos ht,lift,bind_tc_ok,hnext,block_P,block_TWEAK,block_m31_add,block_write_block_rounds_loop0_loop0,block_write_block_rounds_loop0,block_write_block_rounds,block_write_block_ends_loop,block_write_block_ends,block_write_block,block_node_pre_loop,block_node_pre,block_node_absorb_loop,block_node_absorb,block_sponge_init,block_sponge_absorb_loop,block_sponge_absorb,poseidon_P,poseidon_EXTERNAL_INITIAL,poseidon_EXTERNAL_FINAL,poseidon_INTERNAL,poseidon_INTERNAL_SHIFTS,poseidon_m31_add,poseidon_m31_mul,poseidon_pow5,poseidon_mat4,poseidon_ext_groups_loop,poseidon_ext_groups,poseidon_ext_sums_loop,poseidon_ext_sums,poseidon_ext_add_loop,poseidon_ext_add,poseidon_external_linear,poseidon_int_part_sum_loop,poseidon_int_part_sum,poseidon_internal_linear_loop,poseidon_internal_linear,poseidon_sbox_full_loop,poseidon_sbox_full,poseidon_full_round,poseidon_internal_round]
    · have ht : ¬i < 8#usize := by simpa [UScalar.lt_equiv] using hit
      simp only [if_neg ht]

theorem poseidon_absorb_into (pre : Array Std.U32 16#usize) (absorb : Array Std.U32 16#usize) :
    aspis_r0_poseidon_copy.absorb_into pre absorb = R0PoseidonCopy.absorb_into pre absorb := by
  simp only [aspis_r0_poseidon_copy.absorb_into,R0PoseidonCopy.absorb_into,block_P,block_TWEAK,block_m31_add,block_write_block_rounds_loop0_loop0,block_write_block_rounds_loop0,block_write_block_rounds,block_write_block_ends_loop,block_write_block_ends,block_write_block,block_node_pre_loop,block_node_pre,block_node_absorb_loop,block_node_absorb,block_sponge_init,block_sponge_absorb_loop,block_sponge_absorb,poseidon_P,poseidon_EXTERNAL_INITIAL,poseidon_EXTERNAL_FINAL,poseidon_INTERNAL,poseidon_INTERNAL_SHIFTS,poseidon_m31_add,poseidon_m31_mul,poseidon_pow5,poseidon_mat4,poseidon_ext_groups_loop,poseidon_ext_groups,poseidon_ext_sums_loop,poseidon_ext_sums,poseidon_ext_add_loop,poseidon_ext_add,poseidon_external_linear,poseidon_int_part_sum_loop,poseidon_int_part_sum,poseidon_internal_linear_loop,poseidon_internal_linear,poseidon_sbox_full_loop,poseidon_sbox_full,poseidon_full_round,poseidon_internal_round,poseidon_absorb_into_loop]

theorem poseidon_leading_pair (pre : Array Std.U32 16#usize) (absorb : Array Std.U32 16#usize) (c0 : Array Std.U32 16#usize) (c1 : Array Std.U32 16#usize) :
    aspis_r0_poseidon_copy.leading_pair pre absorb c0 c1 = R0PoseidonCopy.leading_pair pre absorb c0 c1 := by
  simp only [aspis_r0_poseidon_copy.leading_pair,R0PoseidonCopy.leading_pair,block_P,block_TWEAK,block_m31_add,block_write_block_rounds_loop0_loop0,block_write_block_rounds_loop0,block_write_block_rounds,block_write_block_ends_loop,block_write_block_ends,block_write_block,block_node_pre_loop,block_node_pre,block_node_absorb_loop,block_node_absorb,block_sponge_init,block_sponge_absorb_loop,block_sponge_absorb,poseidon_P,poseidon_EXTERNAL_INITIAL,poseidon_EXTERNAL_FINAL,poseidon_INTERNAL,poseidon_INTERNAL_SHIFTS,poseidon_m31_add,poseidon_m31_mul,poseidon_pow5,poseidon_mat4,poseidon_ext_groups_loop,poseidon_ext_groups,poseidon_ext_sums_loop,poseidon_ext_sums,poseidon_ext_add_loop,poseidon_ext_add,poseidon_external_linear,poseidon_int_part_sum_loop,poseidon_int_part_sum,poseidon_internal_linear_loop,poseidon_internal_linear,poseidon_sbox_full_loop,poseidon_sbox_full,poseidon_full_round,poseidon_internal_round,poseidon_absorb_into_loop,poseidon_absorb_into]

theorem poseidon_apply_round (state : Array Std.U32 16#usize) (round : Std.Usize) :
    aspis_r0_poseidon_copy.apply_round state round = R0PoseidonCopy.apply_round state round := by
  simp only [aspis_r0_poseidon_copy.apply_round,R0PoseidonCopy.apply_round,block_P,block_TWEAK,block_m31_add,block_write_block_rounds_loop0_loop0,block_write_block_rounds_loop0,block_write_block_rounds,block_write_block_ends_loop,block_write_block_ends,block_write_block,block_node_pre_loop,block_node_pre,block_node_absorb_loop,block_node_absorb,block_sponge_init,block_sponge_absorb_loop,block_sponge_absorb,poseidon_P,poseidon_EXTERNAL_INITIAL,poseidon_EXTERNAL_FINAL,poseidon_INTERNAL,poseidon_INTERNAL_SHIFTS,poseidon_m31_add,poseidon_m31_mul,poseidon_pow5,poseidon_mat4,poseidon_ext_groups_loop,poseidon_ext_groups,poseidon_ext_sums_loop,poseidon_ext_sums,poseidon_ext_add_loop,poseidon_ext_add,poseidon_external_linear,poseidon_int_part_sum_loop,poseidon_int_part_sum,poseidon_internal_linear_loop,poseidon_internal_linear,poseidon_sbox_full_loop,poseidon_sbox_full,poseidon_full_round,poseidon_internal_round,poseidon_absorb_into_loop,poseidon_absorb_into,poseidon_leading_pair]

theorem poseidon_perm_rounds_loop (rounds : Array (Array Std.U32 16#usize) 11#usize) (state : Array Std.U32 16#usize) (k : Std.Usize) :
    aspis_r0_poseidon_copy.perm_rounds_loop rounds state k = R0PoseidonCopy.perm_rounds_loop rounds state k := by
  generalize he : 11-k.val = remaining
  induction remaining using Nat.strong_induction_on generalizing rounds state k with
  | h remaining ih =>
    rw [aspis_r0_poseidon_copy.perm_rounds_loop,R0PoseidonCopy.perm_rounds_loop]
    by_cases hit : k.val < 11
    · have ht : k < 11#usize := by simpa [UScalar.lt_equiv] using hit
      have hn : (Usize.wrapping_add k 1#usize).val = k.val+1 := by
        rw [uadd _ _ (by simp; omega)]; rfl
      have hnext : ∀ (rounds : Array (Array Std.U32 16#usize) 11#usize) (state : Array Std.U32 16#usize),
          aspis_r0_poseidon_copy.perm_rounds_loop rounds state (Usize.wrapping_add k 1#usize) = R0PoseidonCopy.perm_rounds_loop rounds state (Usize.wrapping_add k 1#usize) := by
        intros rounds state
        exact ih (11-(Usize.wrapping_add k 1#usize).val) (by omega) rounds state (Usize.wrapping_add k 1#usize) rfl
      simp only [if_pos ht,lift,bind_tc_ok,hnext,block_P,block_TWEAK,block_m31_add,block_write_block_rounds_loop0_loop0,block_write_block_rounds_loop0,block_write_block_rounds,block_write_block_ends_loop,block_write_block_ends,block_write_block,block_node_pre_loop,block_node_pre,block_node_absorb_loop,block_node_absorb,block_sponge_init,block_sponge_absorb_loop,block_sponge_absorb,poseidon_P,poseidon_EXTERNAL_INITIAL,poseidon_EXTERNAL_FINAL,poseidon_INTERNAL,poseidon_INTERNAL_SHIFTS,poseidon_m31_add,poseidon_m31_mul,poseidon_pow5,poseidon_mat4,poseidon_ext_groups_loop,poseidon_ext_groups,poseidon_ext_sums_loop,poseidon_ext_sums,poseidon_ext_add_loop,poseidon_ext_add,poseidon_external_linear,poseidon_int_part_sum_loop,poseidon_int_part_sum,poseidon_internal_linear_loop,poseidon_internal_linear,poseidon_sbox_full_loop,poseidon_sbox_full,poseidon_full_round,poseidon_internal_round,poseidon_absorb_into_loop,poseidon_absorb_into,poseidon_leading_pair,poseidon_apply_round]
    · have ht : ¬k < 11#usize := by simpa [UScalar.lt_equiv] using hit
      simp only [if_neg ht]

theorem poseidon_perm_rounds (pre : Array Std.U32 16#usize) (absorb : Array Std.U32 16#usize) :
    aspis_r0_poseidon_copy.perm_rounds pre absorb = R0PoseidonCopy.perm_rounds pre absorb := by
  simp only [aspis_r0_poseidon_copy.perm_rounds,R0PoseidonCopy.perm_rounds,block_P,block_TWEAK,block_m31_add,block_write_block_rounds_loop0_loop0,block_write_block_rounds_loop0,block_write_block_rounds,block_write_block_ends_loop,block_write_block_ends,block_write_block,block_node_pre_loop,block_node_pre,block_node_absorb_loop,block_node_absorb,block_sponge_init,block_sponge_absorb_loop,block_sponge_absorb,poseidon_P,poseidon_EXTERNAL_INITIAL,poseidon_EXTERNAL_FINAL,poseidon_INTERNAL,poseidon_INTERNAL_SHIFTS,poseidon_m31_add,poseidon_m31_mul,poseidon_pow5,poseidon_mat4,poseidon_ext_groups_loop,poseidon_ext_groups,poseidon_ext_sums_loop,poseidon_ext_sums,poseidon_ext_add_loop,poseidon_ext_add,poseidon_external_linear,poseidon_int_part_sum_loop,poseidon_int_part_sum,poseidon_internal_linear_loop,poseidon_internal_linear,poseidon_sbox_full_loop,poseidon_sbox_full,poseidon_full_round,poseidon_internal_round,poseidon_absorb_into_loop,poseidon_absorb_into,poseidon_leading_pair,poseidon_apply_round,poseidon_perm_rounds_loop]

#print axioms block_P
#print axioms block_TWEAK
#print axioms block_m31_add
#print axioms block_write_block_rounds_loop0_loop0
#print axioms block_write_block_rounds_loop0
#print axioms block_write_block_rounds
#print axioms block_write_block_ends_loop
#print axioms block_write_block_ends
#print axioms block_write_block
#print axioms block_node_pre_loop
#print axioms block_node_pre
#print axioms block_node_absorb_loop
#print axioms block_node_absorb
#print axioms block_sponge_init
#print axioms block_sponge_absorb_loop
#print axioms block_sponge_absorb
#print axioms poseidon_P
#print axioms poseidon_EXTERNAL_INITIAL
#print axioms poseidon_EXTERNAL_FINAL
#print axioms poseidon_INTERNAL
#print axioms poseidon_INTERNAL_SHIFTS
#print axioms poseidon_m31_add
#print axioms poseidon_m31_mul
#print axioms poseidon_pow5
#print axioms poseidon_mat4
#print axioms poseidon_ext_groups_loop
#print axioms poseidon_ext_groups
#print axioms poseidon_ext_sums_loop
#print axioms poseidon_ext_sums
#print axioms poseidon_ext_add_loop
#print axioms poseidon_ext_add
#print axioms poseidon_external_linear
#print axioms poseidon_int_part_sum_loop
#print axioms poseidon_int_part_sum
#print axioms poseidon_internal_linear_loop
#print axioms poseidon_internal_linear
#print axioms poseidon_sbox_full_loop
#print axioms poseidon_sbox_full
#print axioms poseidon_full_round
#print axioms poseidon_internal_round
#print axioms poseidon_absorb_into_loop
#print axioms poseidon_absorb_into
#print axioms poseidon_leading_pair
#print axioms poseidon_apply_round
#print axioms poseidon_perm_rounds_loop
#print axioms poseidon_perm_rounds
end R1Z.PV_Src_Forest_PrimitiveDigests
