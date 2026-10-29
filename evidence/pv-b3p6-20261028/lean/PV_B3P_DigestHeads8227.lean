import PV_B3P_DigestHead24227
import PV_B3P_DigestEntryFactor8227
import PV_B3P_DigestStage00227
import PV_B3P_DigestStage01227
import PV_B3P_DigestStage02227
import PV_B3P_DigestStage03227
import PV_B3P_DigestStage04227
import PV_B3P_DigestStage05227
import PV_B3P_DigestStage06227
import PV_B3P_DigestStage07227
import PV_B3P_DigestStage08227
import PV_B3P_DigestStage09227
import PV_B3P_DigestStage10227
import PV_B3P_DigestStage11227
import PV_B3P_DigestStage12227
import PV_B3P_DigestStage13227
import PV_B3P_DigestStage14227
import PV_B3P_DigestStage15227
import PV_B3P_DigestStage16227
import PV_B3P_DigestStage17227
import PV_B3P_DigestStage18227
import PV_B3P_DigestStage19227
import PV_B3P_DigestStage20227
import PV_B3P_DigestStage21227
import PV_B3P_DigestStage22227
import PV_B3P_DigestStage23227
namespace PV_B3P_Success227
open Aeneas Aeneas.Std PV_B3P_227
set_option autoImplicit false
attribute [local irreducible] reference_terminal.add_digest_binding reference_copy_terminal.Selectors.row reference_terminal.empty_root reference_terminal.digest227 reference_terminal.bounded_append_carry

def digest_head_23 (public1 : reference_terminal.SemanticPublic)
    (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
    (selectors : reference_copy_terminal.Selectors) (output : Digest8Q) : Result Digest8Q := do
  let block19 ← lift (Std.Usize.wrapping_add 34#usize 19#usize)
  let i44 ←
    lift (Std.U64.wrapping_shr public1.transition.live_snapshot.next_pair_index
      19#u32)
  let i45 ← lift (i44 &&& 1#u64)
  let digests24 ←
    if i45 = 0#u64
    then
      do
      let i46 ← lift (Std.Usize.wrapping_mul block19 16#usize)
      let q3 ← reference_copy_terminal.Selectors.row selectors i46
      let a ← reference_terminal.empty_root 19#usize
      reference_terminal.add_digest_binding output q3 openings.z
        aspis_statement.poseidon2.RATE a true
    else
      do
      let i46 ← lift (Std.Usize.wrapping_mul block19 16#usize)
      let i47 ← lift (Std.Usize.wrapping_add i46 12#usize)
      let q3 ← reference_copy_terminal.Selectors.row selectors i47
      let a ←
        reference_terminal.digest227 public1.transition.live_snapshot.frontier
          19#usize
      reference_terminal.add_digest_binding output q3 openings.z 0#usize a
        false
  digest_raw_24 public1 openings selectors digests24

theorem digest_head_23_factor (public1 : reference_terminal.SemanticPublic)
    (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
    (selectors : reference_copy_terminal.Selectors) (output : Digest8Q) :
    digest_raw_23 public1 openings selectors output = digest_head_23 public1 openings selectors output := by
  rfl

attribute [local irreducible] digest_raw_24

theorem digest_head_23_equation (public1 : reference_terminal.SemanticPublic)
    (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
    (selectors : reference_copy_terminal.Selectors) (output : Digest8Q) :
    digest_head_23 public1 openings selectors output = digest_stage_23 public1 openings selectors output >>= digest_raw_24 public1 openings selectors := by
  simp only [digest_head_23,digest_stage_23,digest_assoc,digest_if_bind,digest_option_bind]

theorem digest_raw_23_success (public1 : reference_terminal.SemanticPublic)
    (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
    (selectors : reference_copy_terminal.Selectors) (output : Digest8Q) :
    Success (digest_raw_23 public1 openings selectors output) := by
  rw [digest_head_23_factor,digest_head_23_equation]
  apply bind
  · exact digest_stage_23_success public1 openings selectors output
  intro next
  exact digest_raw_24_success public1 openings selectors next

#print axioms digest_head_23_factor
#print axioms digest_head_23_equation
#print axioms digest_raw_23_success

def digest_head_22 (public1 : reference_terminal.SemanticPublic)
    (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
    (selectors : reference_copy_terminal.Selectors) (output : Digest8Q) : Result Digest8Q := do
  let block18 ← lift (Std.Usize.wrapping_add 34#usize 18#usize)
  let i42 ←
    lift (Std.U64.wrapping_shr public1.transition.live_snapshot.next_pair_index
      18#u32)
  let i43 ← lift (i42 &&& 1#u64)
  let digests23 ←
    if i43 = 0#u64
    then
      do
      let i44 ← lift (Std.Usize.wrapping_mul block18 16#usize)
      let q3 ← reference_copy_terminal.Selectors.row selectors i44
      let a ← reference_terminal.empty_root 18#usize
      reference_terminal.add_digest_binding output q3 openings.z
        aspis_statement.poseidon2.RATE a true
    else
      do
      let i44 ← lift (Std.Usize.wrapping_mul block18 16#usize)
      let i45 ← lift (Std.Usize.wrapping_add i44 12#usize)
      let q3 ← reference_copy_terminal.Selectors.row selectors i45
      let a ←
        reference_terminal.digest227 public1.transition.live_snapshot.frontier
          18#usize
      reference_terminal.add_digest_binding output q3 openings.z 0#usize a
        false
  digest_raw_23 public1 openings selectors digests23

theorem digest_head_22_factor (public1 : reference_terminal.SemanticPublic)
    (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
    (selectors : reference_copy_terminal.Selectors) (output : Digest8Q) :
    digest_raw_22 public1 openings selectors output = digest_head_22 public1 openings selectors output := by
  rfl

attribute [local irreducible] digest_raw_23

theorem digest_head_22_equation (public1 : reference_terminal.SemanticPublic)
    (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
    (selectors : reference_copy_terminal.Selectors) (output : Digest8Q) :
    digest_head_22 public1 openings selectors output = digest_stage_22 public1 openings selectors output >>= digest_raw_23 public1 openings selectors := by
  simp only [digest_head_22,digest_stage_22,digest_assoc,digest_if_bind,digest_option_bind]

theorem digest_raw_22_success (public1 : reference_terminal.SemanticPublic)
    (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
    (selectors : reference_copy_terminal.Selectors) (output : Digest8Q) :
    Success (digest_raw_22 public1 openings selectors output) := by
  rw [digest_head_22_factor,digest_head_22_equation]
  apply bind
  · exact digest_stage_22_success public1 openings selectors output
  intro next
  exact digest_raw_23_success public1 openings selectors next

#print axioms digest_head_22_factor
#print axioms digest_head_22_equation
#print axioms digest_raw_22_success

def digest_head_21 (public1 : reference_terminal.SemanticPublic)
    (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
    (selectors : reference_copy_terminal.Selectors) (output : Digest8Q) : Result Digest8Q := do
  let block17 ← lift (Std.Usize.wrapping_add 34#usize 17#usize)
  let i40 ←
    lift (Std.U64.wrapping_shr public1.transition.live_snapshot.next_pair_index
      17#u32)
  let i41 ← lift (i40 &&& 1#u64)
  let digests22 ←
    if i41 = 0#u64
    then
      do
      let i42 ← lift (Std.Usize.wrapping_mul block17 16#usize)
      let q3 ← reference_copy_terminal.Selectors.row selectors i42
      let a ← reference_terminal.empty_root 17#usize
      reference_terminal.add_digest_binding output q3 openings.z
        aspis_statement.poseidon2.RATE a true
    else
      do
      let i42 ← lift (Std.Usize.wrapping_mul block17 16#usize)
      let i43 ← lift (Std.Usize.wrapping_add i42 12#usize)
      let q3 ← reference_copy_terminal.Selectors.row selectors i43
      let a ←
        reference_terminal.digest227 public1.transition.live_snapshot.frontier
          17#usize
      reference_terminal.add_digest_binding output q3 openings.z 0#usize a
        false
  digest_raw_22 public1 openings selectors digests22

theorem digest_head_21_factor (public1 : reference_terminal.SemanticPublic)
    (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
    (selectors : reference_copy_terminal.Selectors) (output : Digest8Q) :
    digest_raw_21 public1 openings selectors output = digest_head_21 public1 openings selectors output := by
  rfl

attribute [local irreducible] digest_raw_22

theorem digest_head_21_equation (public1 : reference_terminal.SemanticPublic)
    (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
    (selectors : reference_copy_terminal.Selectors) (output : Digest8Q) :
    digest_head_21 public1 openings selectors output = digest_stage_21 public1 openings selectors output >>= digest_raw_22 public1 openings selectors := by
  simp only [digest_head_21,digest_stage_21,digest_assoc,digest_if_bind,digest_option_bind]

theorem digest_raw_21_success (public1 : reference_terminal.SemanticPublic)
    (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
    (selectors : reference_copy_terminal.Selectors) (output : Digest8Q) :
    Success (digest_raw_21 public1 openings selectors output) := by
  rw [digest_head_21_factor,digest_head_21_equation]
  apply bind
  · exact digest_stage_21_success public1 openings selectors output
  intro next
  exact digest_raw_22_success public1 openings selectors next

#print axioms digest_head_21_factor
#print axioms digest_head_21_equation
#print axioms digest_raw_21_success

def digest_head_20 (public1 : reference_terminal.SemanticPublic)
    (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
    (selectors : reference_copy_terminal.Selectors) (output : Digest8Q) : Result Digest8Q := do
  let block16 ← lift (Std.Usize.wrapping_add 34#usize 16#usize)
  let i38 ←
    lift (Std.U64.wrapping_shr public1.transition.live_snapshot.next_pair_index
      16#u32)
  let i39 ← lift (i38 &&& 1#u64)
  let digests21 ←
    if i39 = 0#u64
    then
      do
      let i40 ← lift (Std.Usize.wrapping_mul block16 16#usize)
      let q3 ← reference_copy_terminal.Selectors.row selectors i40
      let a ← reference_terminal.empty_root 16#usize
      reference_terminal.add_digest_binding output q3 openings.z
        aspis_statement.poseidon2.RATE a true
    else
      do
      let i40 ← lift (Std.Usize.wrapping_mul block16 16#usize)
      let i41 ← lift (Std.Usize.wrapping_add i40 12#usize)
      let q3 ← reference_copy_terminal.Selectors.row selectors i41
      let a ←
        reference_terminal.digest227 public1.transition.live_snapshot.frontier
          16#usize
      reference_terminal.add_digest_binding output q3 openings.z 0#usize a
        false
  digest_raw_21 public1 openings selectors digests21

theorem digest_head_20_factor (public1 : reference_terminal.SemanticPublic)
    (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
    (selectors : reference_copy_terminal.Selectors) (output : Digest8Q) :
    digest_raw_20 public1 openings selectors output = digest_head_20 public1 openings selectors output := by
  rfl

attribute [local irreducible] digest_raw_21

theorem digest_head_20_equation (public1 : reference_terminal.SemanticPublic)
    (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
    (selectors : reference_copy_terminal.Selectors) (output : Digest8Q) :
    digest_head_20 public1 openings selectors output = digest_stage_20 public1 openings selectors output >>= digest_raw_21 public1 openings selectors := by
  simp only [digest_head_20,digest_stage_20,digest_assoc,digest_if_bind,digest_option_bind]

theorem digest_raw_20_success (public1 : reference_terminal.SemanticPublic)
    (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
    (selectors : reference_copy_terminal.Selectors) (output : Digest8Q) :
    Success (digest_raw_20 public1 openings selectors output) := by
  rw [digest_head_20_factor,digest_head_20_equation]
  apply bind
  · exact digest_stage_20_success public1 openings selectors output
  intro next
  exact digest_raw_21_success public1 openings selectors next

#print axioms digest_head_20_factor
#print axioms digest_head_20_equation
#print axioms digest_raw_20_success

def digest_head_19 (public1 : reference_terminal.SemanticPublic)
    (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
    (selectors : reference_copy_terminal.Selectors) (output : Digest8Q) : Result Digest8Q := do
  let block15 ← lift (Std.Usize.wrapping_add 34#usize 15#usize)
  let i36 ←
    lift (Std.U64.wrapping_shr public1.transition.live_snapshot.next_pair_index
      15#u32)
  let i37 ← lift (i36 &&& 1#u64)
  let digests20 ←
    if i37 = 0#u64
    then
      do
      let i38 ← lift (Std.Usize.wrapping_mul block15 16#usize)
      let q3 ← reference_copy_terminal.Selectors.row selectors i38
      let a ← reference_terminal.empty_root 15#usize
      reference_terminal.add_digest_binding output q3 openings.z
        aspis_statement.poseidon2.RATE a true
    else
      do
      let i38 ← lift (Std.Usize.wrapping_mul block15 16#usize)
      let i39 ← lift (Std.Usize.wrapping_add i38 12#usize)
      let q3 ← reference_copy_terminal.Selectors.row selectors i39
      let a ←
        reference_terminal.digest227 public1.transition.live_snapshot.frontier
          15#usize
      reference_terminal.add_digest_binding output q3 openings.z 0#usize a
        false
  digest_raw_20 public1 openings selectors digests20

theorem digest_head_19_factor (public1 : reference_terminal.SemanticPublic)
    (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
    (selectors : reference_copy_terminal.Selectors) (output : Digest8Q) :
    digest_raw_19 public1 openings selectors output = digest_head_19 public1 openings selectors output := by
  rfl

attribute [local irreducible] digest_raw_20

theorem digest_head_19_equation (public1 : reference_terminal.SemanticPublic)
    (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
    (selectors : reference_copy_terminal.Selectors) (output : Digest8Q) :
    digest_head_19 public1 openings selectors output = digest_stage_19 public1 openings selectors output >>= digest_raw_20 public1 openings selectors := by
  simp only [digest_head_19,digest_stage_19,digest_assoc,digest_if_bind,digest_option_bind]

theorem digest_raw_19_success (public1 : reference_terminal.SemanticPublic)
    (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
    (selectors : reference_copy_terminal.Selectors) (output : Digest8Q) :
    Success (digest_raw_19 public1 openings selectors output) := by
  rw [digest_head_19_factor,digest_head_19_equation]
  apply bind
  · exact digest_stage_19_success public1 openings selectors output
  intro next
  exact digest_raw_20_success public1 openings selectors next

#print axioms digest_head_19_factor
#print axioms digest_head_19_equation
#print axioms digest_raw_19_success

def digest_head_18 (public1 : reference_terminal.SemanticPublic)
    (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
    (selectors : reference_copy_terminal.Selectors) (output : Digest8Q) : Result Digest8Q := do
  let block14 ← lift (Std.Usize.wrapping_add 34#usize 14#usize)
  let i34 ←
    lift (Std.U64.wrapping_shr public1.transition.live_snapshot.next_pair_index
      14#u32)
  let i35 ← lift (i34 &&& 1#u64)
  let digests19 ←
    if i35 = 0#u64
    then
      do
      let i36 ← lift (Std.Usize.wrapping_mul block14 16#usize)
      let q3 ← reference_copy_terminal.Selectors.row selectors i36
      let a ← reference_terminal.empty_root 14#usize
      reference_terminal.add_digest_binding output q3 openings.z
        aspis_statement.poseidon2.RATE a true
    else
      do
      let i36 ← lift (Std.Usize.wrapping_mul block14 16#usize)
      let i37 ← lift (Std.Usize.wrapping_add i36 12#usize)
      let q3 ← reference_copy_terminal.Selectors.row selectors i37
      let a ←
        reference_terminal.digest227 public1.transition.live_snapshot.frontier
          14#usize
      reference_terminal.add_digest_binding output q3 openings.z 0#usize a
        false
  digest_raw_19 public1 openings selectors digests19

theorem digest_head_18_factor (public1 : reference_terminal.SemanticPublic)
    (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
    (selectors : reference_copy_terminal.Selectors) (output : Digest8Q) :
    digest_raw_18 public1 openings selectors output = digest_head_18 public1 openings selectors output := by
  rfl

attribute [local irreducible] digest_raw_19

theorem digest_head_18_equation (public1 : reference_terminal.SemanticPublic)
    (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
    (selectors : reference_copy_terminal.Selectors) (output : Digest8Q) :
    digest_head_18 public1 openings selectors output = digest_stage_18 public1 openings selectors output >>= digest_raw_19 public1 openings selectors := by
  simp only [digest_head_18,digest_stage_18,digest_assoc,digest_if_bind,digest_option_bind]

theorem digest_raw_18_success (public1 : reference_terminal.SemanticPublic)
    (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
    (selectors : reference_copy_terminal.Selectors) (output : Digest8Q) :
    Success (digest_raw_18 public1 openings selectors output) := by
  rw [digest_head_18_factor,digest_head_18_equation]
  apply bind
  · exact digest_stage_18_success public1 openings selectors output
  intro next
  exact digest_raw_19_success public1 openings selectors next

#print axioms digest_head_18_factor
#print axioms digest_head_18_equation
#print axioms digest_raw_18_success

def digest_head_17 (public1 : reference_terminal.SemanticPublic)
    (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
    (selectors : reference_copy_terminal.Selectors) (output : Digest8Q) : Result Digest8Q := do
  let block13 ← lift (Std.Usize.wrapping_add 34#usize 13#usize)
  let i32 ←
    lift (Std.U64.wrapping_shr public1.transition.live_snapshot.next_pair_index
      13#u32)
  let i33 ← lift (i32 &&& 1#u64)
  let digests18 ←
    if i33 = 0#u64
    then
      do
      let i34 ← lift (Std.Usize.wrapping_mul block13 16#usize)
      let q3 ← reference_copy_terminal.Selectors.row selectors i34
      let a ← reference_terminal.empty_root 13#usize
      reference_terminal.add_digest_binding output q3 openings.z
        aspis_statement.poseidon2.RATE a true
    else
      do
      let i34 ← lift (Std.Usize.wrapping_mul block13 16#usize)
      let i35 ← lift (Std.Usize.wrapping_add i34 12#usize)
      let q3 ← reference_copy_terminal.Selectors.row selectors i35
      let a ←
        reference_terminal.digest227 public1.transition.live_snapshot.frontier
          13#usize
      reference_terminal.add_digest_binding output q3 openings.z 0#usize a
        false
  digest_raw_18 public1 openings selectors digests18

theorem digest_head_17_factor (public1 : reference_terminal.SemanticPublic)
    (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
    (selectors : reference_copy_terminal.Selectors) (output : Digest8Q) :
    digest_raw_17 public1 openings selectors output = digest_head_17 public1 openings selectors output := by
  rfl

attribute [local irreducible] digest_raw_18

theorem digest_head_17_equation (public1 : reference_terminal.SemanticPublic)
    (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
    (selectors : reference_copy_terminal.Selectors) (output : Digest8Q) :
    digest_head_17 public1 openings selectors output = digest_stage_17 public1 openings selectors output >>= digest_raw_18 public1 openings selectors := by
  simp only [digest_head_17,digest_stage_17,digest_assoc,digest_if_bind,digest_option_bind]

theorem digest_raw_17_success (public1 : reference_terminal.SemanticPublic)
    (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
    (selectors : reference_copy_terminal.Selectors) (output : Digest8Q) :
    Success (digest_raw_17 public1 openings selectors output) := by
  rw [digest_head_17_factor,digest_head_17_equation]
  apply bind
  · exact digest_stage_17_success public1 openings selectors output
  intro next
  exact digest_raw_18_success public1 openings selectors next

#print axioms digest_head_17_factor
#print axioms digest_head_17_equation
#print axioms digest_raw_17_success

def digest_head_16 (public1 : reference_terminal.SemanticPublic)
    (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
    (selectors : reference_copy_terminal.Selectors) (output : Digest8Q) : Result Digest8Q := do
  let block12 ← lift (Std.Usize.wrapping_add 34#usize 12#usize)
  let i30 ←
    lift (Std.U64.wrapping_shr public1.transition.live_snapshot.next_pair_index
      12#u32)
  let i31 ← lift (i30 &&& 1#u64)
  let digests17 ←
    if i31 = 0#u64
    then
      do
      let i32 ← lift (Std.Usize.wrapping_mul block12 16#usize)
      let q3 ← reference_copy_terminal.Selectors.row selectors i32
      let a ← reference_terminal.empty_root 12#usize
      reference_terminal.add_digest_binding output q3 openings.z
        aspis_statement.poseidon2.RATE a true
    else
      do
      let i32 ← lift (Std.Usize.wrapping_mul block12 16#usize)
      let i33 ← lift (Std.Usize.wrapping_add i32 12#usize)
      let q3 ← reference_copy_terminal.Selectors.row selectors i33
      let a ←
        reference_terminal.digest227 public1.transition.live_snapshot.frontier
          12#usize
      reference_terminal.add_digest_binding output q3 openings.z 0#usize a
        false
  digest_raw_17 public1 openings selectors digests17

theorem digest_head_16_factor (public1 : reference_terminal.SemanticPublic)
    (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
    (selectors : reference_copy_terminal.Selectors) (output : Digest8Q) :
    digest_raw_16 public1 openings selectors output = digest_head_16 public1 openings selectors output := by
  rfl

attribute [local irreducible] digest_raw_17

theorem digest_head_16_equation (public1 : reference_terminal.SemanticPublic)
    (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
    (selectors : reference_copy_terminal.Selectors) (output : Digest8Q) :
    digest_head_16 public1 openings selectors output = digest_stage_16 public1 openings selectors output >>= digest_raw_17 public1 openings selectors := by
  simp only [digest_head_16,digest_stage_16,digest_assoc,digest_if_bind,digest_option_bind]

theorem digest_raw_16_success (public1 : reference_terminal.SemanticPublic)
    (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
    (selectors : reference_copy_terminal.Selectors) (output : Digest8Q) :
    Success (digest_raw_16 public1 openings selectors output) := by
  rw [digest_head_16_factor,digest_head_16_equation]
  apply bind
  · exact digest_stage_16_success public1 openings selectors output
  intro next
  exact digest_raw_17_success public1 openings selectors next

#print axioms digest_head_16_factor
#print axioms digest_head_16_equation
#print axioms digest_raw_16_success

def digest_head_15 (public1 : reference_terminal.SemanticPublic)
    (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
    (selectors : reference_copy_terminal.Selectors) (output : Digest8Q) : Result Digest8Q := do
  let block11 ← lift (Std.Usize.wrapping_add 34#usize 11#usize)
  let i28 ←
    lift (Std.U64.wrapping_shr public1.transition.live_snapshot.next_pair_index
      11#u32)
  let i29 ← lift (i28 &&& 1#u64)
  let digests16 ←
    if i29 = 0#u64
    then
      do
      let i30 ← lift (Std.Usize.wrapping_mul block11 16#usize)
      let q3 ← reference_copy_terminal.Selectors.row selectors i30
      let a ← reference_terminal.empty_root 11#usize
      reference_terminal.add_digest_binding output q3 openings.z
        aspis_statement.poseidon2.RATE a true
    else
      do
      let i30 ← lift (Std.Usize.wrapping_mul block11 16#usize)
      let i31 ← lift (Std.Usize.wrapping_add i30 12#usize)
      let q3 ← reference_copy_terminal.Selectors.row selectors i31
      let a ←
        reference_terminal.digest227 public1.transition.live_snapshot.frontier
          11#usize
      reference_terminal.add_digest_binding output q3 openings.z 0#usize a
        false
  digest_raw_16 public1 openings selectors digests16

theorem digest_head_15_factor (public1 : reference_terminal.SemanticPublic)
    (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
    (selectors : reference_copy_terminal.Selectors) (output : Digest8Q) :
    digest_raw_15 public1 openings selectors output = digest_head_15 public1 openings selectors output := by
  rfl

attribute [local irreducible] digest_raw_16

theorem digest_head_15_equation (public1 : reference_terminal.SemanticPublic)
    (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
    (selectors : reference_copy_terminal.Selectors) (output : Digest8Q) :
    digest_head_15 public1 openings selectors output = digest_stage_15 public1 openings selectors output >>= digest_raw_16 public1 openings selectors := by
  simp only [digest_head_15,digest_stage_15,digest_assoc,digest_if_bind,digest_option_bind]

theorem digest_raw_15_success (public1 : reference_terminal.SemanticPublic)
    (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
    (selectors : reference_copy_terminal.Selectors) (output : Digest8Q) :
    Success (digest_raw_15 public1 openings selectors output) := by
  rw [digest_head_15_factor,digest_head_15_equation]
  apply bind
  · exact digest_stage_15_success public1 openings selectors output
  intro next
  exact digest_raw_16_success public1 openings selectors next

#print axioms digest_head_15_factor
#print axioms digest_head_15_equation
#print axioms digest_raw_15_success

def digest_head_14 (public1 : reference_terminal.SemanticPublic)
    (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
    (selectors : reference_copy_terminal.Selectors) (output : Digest8Q) : Result Digest8Q := do
  let block10 ← lift (Std.Usize.wrapping_add 34#usize 10#usize)
  let i26 ←
    lift (Std.U64.wrapping_shr public1.transition.live_snapshot.next_pair_index
      10#u32)
  let i27 ← lift (i26 &&& 1#u64)
  let digests15 ←
    if i27 = 0#u64
    then
      do
      let i28 ← lift (Std.Usize.wrapping_mul block10 16#usize)
      let q3 ← reference_copy_terminal.Selectors.row selectors i28
      let a ← reference_terminal.empty_root 10#usize
      reference_terminal.add_digest_binding output q3 openings.z
        aspis_statement.poseidon2.RATE a true
    else
      do
      let i28 ← lift (Std.Usize.wrapping_mul block10 16#usize)
      let i29 ← lift (Std.Usize.wrapping_add i28 12#usize)
      let q3 ← reference_copy_terminal.Selectors.row selectors i29
      let a ←
        reference_terminal.digest227 public1.transition.live_snapshot.frontier
          10#usize
      reference_terminal.add_digest_binding output q3 openings.z 0#usize a
        false
  digest_raw_15 public1 openings selectors digests15

theorem digest_head_14_factor (public1 : reference_terminal.SemanticPublic)
    (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
    (selectors : reference_copy_terminal.Selectors) (output : Digest8Q) :
    digest_raw_14 public1 openings selectors output = digest_head_14 public1 openings selectors output := by
  rfl

attribute [local irreducible] digest_raw_15

theorem digest_head_14_equation (public1 : reference_terminal.SemanticPublic)
    (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
    (selectors : reference_copy_terminal.Selectors) (output : Digest8Q) :
    digest_head_14 public1 openings selectors output = digest_stage_14 public1 openings selectors output >>= digest_raw_15 public1 openings selectors := by
  simp only [digest_head_14,digest_stage_14,digest_assoc,digest_if_bind,digest_option_bind]

theorem digest_raw_14_success (public1 : reference_terminal.SemanticPublic)
    (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
    (selectors : reference_copy_terminal.Selectors) (output : Digest8Q) :
    Success (digest_raw_14 public1 openings selectors output) := by
  rw [digest_head_14_factor,digest_head_14_equation]
  apply bind
  · exact digest_stage_14_success public1 openings selectors output
  intro next
  exact digest_raw_15_success public1 openings selectors next

#print axioms digest_head_14_factor
#print axioms digest_head_14_equation
#print axioms digest_raw_14_success

def digest_head_13 (public1 : reference_terminal.SemanticPublic)
    (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
    (selectors : reference_copy_terminal.Selectors) (output : Digest8Q) : Result Digest8Q := do
  let block9 ← lift (Std.Usize.wrapping_add 34#usize 9#usize)
  let i24 ←
    lift (Std.U64.wrapping_shr public1.transition.live_snapshot.next_pair_index
      9#u32)
  let i25 ← lift (i24 &&& 1#u64)
  let digests14 ←
    if i25 = 0#u64
    then
      do
      let i26 ← lift (Std.Usize.wrapping_mul block9 16#usize)
      let q3 ← reference_copy_terminal.Selectors.row selectors i26
      let a ← reference_terminal.empty_root 9#usize
      reference_terminal.add_digest_binding output q3 openings.z
        aspis_statement.poseidon2.RATE a true
    else
      do
      let i26 ← lift (Std.Usize.wrapping_mul block9 16#usize)
      let i27 ← lift (Std.Usize.wrapping_add i26 12#usize)
      let q3 ← reference_copy_terminal.Selectors.row selectors i27
      let a ←
        reference_terminal.digest227 public1.transition.live_snapshot.frontier
          9#usize
      reference_terminal.add_digest_binding output q3 openings.z 0#usize a
        false
  digest_raw_14 public1 openings selectors digests14

theorem digest_head_13_factor (public1 : reference_terminal.SemanticPublic)
    (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
    (selectors : reference_copy_terminal.Selectors) (output : Digest8Q) :
    digest_raw_13 public1 openings selectors output = digest_head_13 public1 openings selectors output := by
  rfl

attribute [local irreducible] digest_raw_14

theorem digest_head_13_equation (public1 : reference_terminal.SemanticPublic)
    (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
    (selectors : reference_copy_terminal.Selectors) (output : Digest8Q) :
    digest_head_13 public1 openings selectors output = digest_stage_13 public1 openings selectors output >>= digest_raw_14 public1 openings selectors := by
  simp only [digest_head_13,digest_stage_13,digest_assoc,digest_if_bind,digest_option_bind]

theorem digest_raw_13_success (public1 : reference_terminal.SemanticPublic)
    (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
    (selectors : reference_copy_terminal.Selectors) (output : Digest8Q) :
    Success (digest_raw_13 public1 openings selectors output) := by
  rw [digest_head_13_factor,digest_head_13_equation]
  apply bind
  · exact digest_stage_13_success public1 openings selectors output
  intro next
  exact digest_raw_14_success public1 openings selectors next

#print axioms digest_head_13_factor
#print axioms digest_head_13_equation
#print axioms digest_raw_13_success

def digest_head_12 (public1 : reference_terminal.SemanticPublic)
    (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
    (selectors : reference_copy_terminal.Selectors) (output : Digest8Q) : Result Digest8Q := do
  let block8 ← lift (Std.Usize.wrapping_add 34#usize 8#usize)
  let i22 ←
    lift (Std.U64.wrapping_shr public1.transition.live_snapshot.next_pair_index
      8#u32)
  let i23 ← lift (i22 &&& 1#u64)
  let digests13 ←
    if i23 = 0#u64
    then
      do
      let i24 ← lift (Std.Usize.wrapping_mul block8 16#usize)
      let q3 ← reference_copy_terminal.Selectors.row selectors i24
      let a ← reference_terminal.empty_root 8#usize
      reference_terminal.add_digest_binding output q3 openings.z
        aspis_statement.poseidon2.RATE a true
    else
      do
      let i24 ← lift (Std.Usize.wrapping_mul block8 16#usize)
      let i25 ← lift (Std.Usize.wrapping_add i24 12#usize)
      let q3 ← reference_copy_terminal.Selectors.row selectors i25
      let a ←
        reference_terminal.digest227 public1.transition.live_snapshot.frontier
          8#usize
      reference_terminal.add_digest_binding output q3 openings.z 0#usize a
        false
  digest_raw_13 public1 openings selectors digests13

theorem digest_head_12_factor (public1 : reference_terminal.SemanticPublic)
    (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
    (selectors : reference_copy_terminal.Selectors) (output : Digest8Q) :
    digest_raw_12 public1 openings selectors output = digest_head_12 public1 openings selectors output := by
  rfl

attribute [local irreducible] digest_raw_13

theorem digest_head_12_equation (public1 : reference_terminal.SemanticPublic)
    (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
    (selectors : reference_copy_terminal.Selectors) (output : Digest8Q) :
    digest_head_12 public1 openings selectors output = digest_stage_12 public1 openings selectors output >>= digest_raw_13 public1 openings selectors := by
  simp only [digest_head_12,digest_stage_12,digest_assoc,digest_if_bind,digest_option_bind]

theorem digest_raw_12_success (public1 : reference_terminal.SemanticPublic)
    (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
    (selectors : reference_copy_terminal.Selectors) (output : Digest8Q) :
    Success (digest_raw_12 public1 openings selectors output) := by
  rw [digest_head_12_factor,digest_head_12_equation]
  apply bind
  · exact digest_stage_12_success public1 openings selectors output
  intro next
  exact digest_raw_13_success public1 openings selectors next

#print axioms digest_head_12_factor
#print axioms digest_head_12_equation
#print axioms digest_raw_12_success

def digest_head_11 (public1 : reference_terminal.SemanticPublic)
    (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
    (selectors : reference_copy_terminal.Selectors) (output : Digest8Q) : Result Digest8Q := do
  let block7 ← lift (Std.Usize.wrapping_add 34#usize 7#usize)
  let i20 ←
    lift (Std.U64.wrapping_shr public1.transition.live_snapshot.next_pair_index
      7#u32)
  let i21 ← lift (i20 &&& 1#u64)
  let digests12 ←
    if i21 = 0#u64
    then
      do
      let i22 ← lift (Std.Usize.wrapping_mul block7 16#usize)
      let q3 ← reference_copy_terminal.Selectors.row selectors i22
      let a ← reference_terminal.empty_root 7#usize
      reference_terminal.add_digest_binding output q3 openings.z
        aspis_statement.poseidon2.RATE a true
    else
      do
      let i22 ← lift (Std.Usize.wrapping_mul block7 16#usize)
      let i23 ← lift (Std.Usize.wrapping_add i22 12#usize)
      let q3 ← reference_copy_terminal.Selectors.row selectors i23
      let a ←
        reference_terminal.digest227 public1.transition.live_snapshot.frontier
          7#usize
      reference_terminal.add_digest_binding output q3 openings.z 0#usize a
        false
  digest_raw_12 public1 openings selectors digests12

theorem digest_head_11_factor (public1 : reference_terminal.SemanticPublic)
    (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
    (selectors : reference_copy_terminal.Selectors) (output : Digest8Q) :
    digest_raw_11 public1 openings selectors output = digest_head_11 public1 openings selectors output := by
  rfl

attribute [local irreducible] digest_raw_12

theorem digest_head_11_equation (public1 : reference_terminal.SemanticPublic)
    (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
    (selectors : reference_copy_terminal.Selectors) (output : Digest8Q) :
    digest_head_11 public1 openings selectors output = digest_stage_11 public1 openings selectors output >>= digest_raw_12 public1 openings selectors := by
  simp only [digest_head_11,digest_stage_11,digest_assoc,digest_if_bind,digest_option_bind]

theorem digest_raw_11_success (public1 : reference_terminal.SemanticPublic)
    (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
    (selectors : reference_copy_terminal.Selectors) (output : Digest8Q) :
    Success (digest_raw_11 public1 openings selectors output) := by
  rw [digest_head_11_factor,digest_head_11_equation]
  apply bind
  · exact digest_stage_11_success public1 openings selectors output
  intro next
  exact digest_raw_12_success public1 openings selectors next

#print axioms digest_head_11_factor
#print axioms digest_head_11_equation
#print axioms digest_raw_11_success

def digest_head_10 (public1 : reference_terminal.SemanticPublic)
    (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
    (selectors : reference_copy_terminal.Selectors) (output : Digest8Q) : Result Digest8Q := do
  let block6 ← lift (Std.Usize.wrapping_add 34#usize 6#usize)
  let i18 ←
    lift (Std.U64.wrapping_shr public1.transition.live_snapshot.next_pair_index
      6#u32)
  let i19 ← lift (i18 &&& 1#u64)
  let digests11 ←
    if i19 = 0#u64
    then
      do
      let i20 ← lift (Std.Usize.wrapping_mul block6 16#usize)
      let q3 ← reference_copy_terminal.Selectors.row selectors i20
      let a ← reference_terminal.empty_root 6#usize
      reference_terminal.add_digest_binding output q3 openings.z
        aspis_statement.poseidon2.RATE a true
    else
      do
      let i20 ← lift (Std.Usize.wrapping_mul block6 16#usize)
      let i21 ← lift (Std.Usize.wrapping_add i20 12#usize)
      let q3 ← reference_copy_terminal.Selectors.row selectors i21
      let a ←
        reference_terminal.digest227 public1.transition.live_snapshot.frontier
          6#usize
      reference_terminal.add_digest_binding output q3 openings.z 0#usize a
        false
  digest_raw_11 public1 openings selectors digests11

theorem digest_head_10_factor (public1 : reference_terminal.SemanticPublic)
    (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
    (selectors : reference_copy_terminal.Selectors) (output : Digest8Q) :
    digest_raw_10 public1 openings selectors output = digest_head_10 public1 openings selectors output := by
  rfl

attribute [local irreducible] digest_raw_11

theorem digest_head_10_equation (public1 : reference_terminal.SemanticPublic)
    (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
    (selectors : reference_copy_terminal.Selectors) (output : Digest8Q) :
    digest_head_10 public1 openings selectors output = digest_stage_10 public1 openings selectors output >>= digest_raw_11 public1 openings selectors := by
  simp only [digest_head_10,digest_stage_10,digest_assoc,digest_if_bind,digest_option_bind]

theorem digest_raw_10_success (public1 : reference_terminal.SemanticPublic)
    (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
    (selectors : reference_copy_terminal.Selectors) (output : Digest8Q) :
    Success (digest_raw_10 public1 openings selectors output) := by
  rw [digest_head_10_factor,digest_head_10_equation]
  apply bind
  · exact digest_stage_10_success public1 openings selectors output
  intro next
  exact digest_raw_11_success public1 openings selectors next

#print axioms digest_head_10_factor
#print axioms digest_head_10_equation
#print axioms digest_raw_10_success

def digest_head_09 (public1 : reference_terminal.SemanticPublic)
    (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
    (selectors : reference_copy_terminal.Selectors) (output : Digest8Q) : Result Digest8Q := do
  let block5 ← lift (Std.Usize.wrapping_add 34#usize 5#usize)
  let i16 ←
    lift (Std.U64.wrapping_shr public1.transition.live_snapshot.next_pair_index
      5#u32)
  let i17 ← lift (i16 &&& 1#u64)
  let digests10 ←
    if i17 = 0#u64
    then
      do
      let i18 ← lift (Std.Usize.wrapping_mul block5 16#usize)
      let q3 ← reference_copy_terminal.Selectors.row selectors i18
      let a ← reference_terminal.empty_root 5#usize
      reference_terminal.add_digest_binding output q3 openings.z
        aspis_statement.poseidon2.RATE a true
    else
      do
      let i18 ← lift (Std.Usize.wrapping_mul block5 16#usize)
      let i19 ← lift (Std.Usize.wrapping_add i18 12#usize)
      let q3 ← reference_copy_terminal.Selectors.row selectors i19
      let a ←
        reference_terminal.digest227 public1.transition.live_snapshot.frontier
          5#usize
      reference_terminal.add_digest_binding output q3 openings.z 0#usize a
        false
  digest_raw_10 public1 openings selectors digests10

theorem digest_head_09_factor (public1 : reference_terminal.SemanticPublic)
    (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
    (selectors : reference_copy_terminal.Selectors) (output : Digest8Q) :
    digest_raw_09 public1 openings selectors output = digest_head_09 public1 openings selectors output := by
  rfl

attribute [local irreducible] digest_raw_10

theorem digest_head_09_equation (public1 : reference_terminal.SemanticPublic)
    (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
    (selectors : reference_copy_terminal.Selectors) (output : Digest8Q) :
    digest_head_09 public1 openings selectors output = digest_stage_09 public1 openings selectors output >>= digest_raw_10 public1 openings selectors := by
  simp only [digest_head_09,digest_stage_09,digest_assoc,digest_if_bind,digest_option_bind]

theorem digest_raw_09_success (public1 : reference_terminal.SemanticPublic)
    (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
    (selectors : reference_copy_terminal.Selectors) (output : Digest8Q) :
    Success (digest_raw_09 public1 openings selectors output) := by
  rw [digest_head_09_factor,digest_head_09_equation]
  apply bind
  · exact digest_stage_09_success public1 openings selectors output
  intro next
  exact digest_raw_10_success public1 openings selectors next

#print axioms digest_head_09_factor
#print axioms digest_head_09_equation
#print axioms digest_raw_09_success

def digest_head_08 (public1 : reference_terminal.SemanticPublic)
    (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
    (selectors : reference_copy_terminal.Selectors) (output : Digest8Q) : Result Digest8Q := do
  let block4 ← lift (Std.Usize.wrapping_add 34#usize 4#usize)
  let i14 ←
    lift (Std.U64.wrapping_shr public1.transition.live_snapshot.next_pair_index
      4#u32)
  let i15 ← lift (i14 &&& 1#u64)
  let digests9 ←
    if i15 = 0#u64
    then
      do
      let i16 ← lift (Std.Usize.wrapping_mul block4 16#usize)
      let q3 ← reference_copy_terminal.Selectors.row selectors i16
      let a ← reference_terminal.empty_root 4#usize
      reference_terminal.add_digest_binding output q3 openings.z
        aspis_statement.poseidon2.RATE a true
    else
      do
      let i16 ← lift (Std.Usize.wrapping_mul block4 16#usize)
      let i17 ← lift (Std.Usize.wrapping_add i16 12#usize)
      let q3 ← reference_copy_terminal.Selectors.row selectors i17
      let a ←
        reference_terminal.digest227 public1.transition.live_snapshot.frontier
          4#usize
      reference_terminal.add_digest_binding output q3 openings.z 0#usize a
        false
  digest_raw_09 public1 openings selectors digests9

theorem digest_head_08_factor (public1 : reference_terminal.SemanticPublic)
    (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
    (selectors : reference_copy_terminal.Selectors) (output : Digest8Q) :
    digest_raw_08 public1 openings selectors output = digest_head_08 public1 openings selectors output := by
  rfl

attribute [local irreducible] digest_raw_09

theorem digest_head_08_equation (public1 : reference_terminal.SemanticPublic)
    (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
    (selectors : reference_copy_terminal.Selectors) (output : Digest8Q) :
    digest_head_08 public1 openings selectors output = digest_stage_08 public1 openings selectors output >>= digest_raw_09 public1 openings selectors := by
  simp only [digest_head_08,digest_stage_08,digest_assoc,digest_if_bind,digest_option_bind]

theorem digest_raw_08_success (public1 : reference_terminal.SemanticPublic)
    (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
    (selectors : reference_copy_terminal.Selectors) (output : Digest8Q) :
    Success (digest_raw_08 public1 openings selectors output) := by
  rw [digest_head_08_factor,digest_head_08_equation]
  apply bind
  · exact digest_stage_08_success public1 openings selectors output
  intro next
  exact digest_raw_09_success public1 openings selectors next

#print axioms digest_head_08_factor
#print axioms digest_head_08_equation
#print axioms digest_raw_08_success

def digest_head_07 (public1 : reference_terminal.SemanticPublic)
    (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
    (selectors : reference_copy_terminal.Selectors) (output : Digest8Q) : Result Digest8Q := do
  let block3 ← lift (Std.Usize.wrapping_add 34#usize 3#usize)
  let i12 ←
    lift (Std.U64.wrapping_shr public1.transition.live_snapshot.next_pair_index
      3#u32)
  let i13 ← lift (i12 &&& 1#u64)
  let digests8 ←
    if i13 = 0#u64
    then
      do
      let i14 ← lift (Std.Usize.wrapping_mul block3 16#usize)
      let q3 ← reference_copy_terminal.Selectors.row selectors i14
      let a ← reference_terminal.empty_root 3#usize
      reference_terminal.add_digest_binding output q3 openings.z
        aspis_statement.poseidon2.RATE a true
    else
      do
      let i14 ← lift (Std.Usize.wrapping_mul block3 16#usize)
      let i15 ← lift (Std.Usize.wrapping_add i14 12#usize)
      let q3 ← reference_copy_terminal.Selectors.row selectors i15
      let a ←
        reference_terminal.digest227 public1.transition.live_snapshot.frontier
          3#usize
      reference_terminal.add_digest_binding output q3 openings.z 0#usize a
        false
  digest_raw_08 public1 openings selectors digests8

theorem digest_head_07_factor (public1 : reference_terminal.SemanticPublic)
    (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
    (selectors : reference_copy_terminal.Selectors) (output : Digest8Q) :
    digest_raw_07 public1 openings selectors output = digest_head_07 public1 openings selectors output := by
  rfl

attribute [local irreducible] digest_raw_08

theorem digest_head_07_equation (public1 : reference_terminal.SemanticPublic)
    (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
    (selectors : reference_copy_terminal.Selectors) (output : Digest8Q) :
    digest_head_07 public1 openings selectors output = digest_stage_07 public1 openings selectors output >>= digest_raw_08 public1 openings selectors := by
  simp only [digest_head_07,digest_stage_07,digest_assoc,digest_if_bind,digest_option_bind]

theorem digest_raw_07_success (public1 : reference_terminal.SemanticPublic)
    (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
    (selectors : reference_copy_terminal.Selectors) (output : Digest8Q) :
    Success (digest_raw_07 public1 openings selectors output) := by
  rw [digest_head_07_factor,digest_head_07_equation]
  apply bind
  · exact digest_stage_07_success public1 openings selectors output
  intro next
  exact digest_raw_08_success public1 openings selectors next

#print axioms digest_head_07_factor
#print axioms digest_head_07_equation
#print axioms digest_raw_07_success

def digest_head_06 (public1 : reference_terminal.SemanticPublic)
    (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
    (selectors : reference_copy_terminal.Selectors) (output : Digest8Q) : Result Digest8Q := do
  let block2 ← lift (Std.Usize.wrapping_add 34#usize 2#usize)
  let i10 ←
    lift (Std.U64.wrapping_shr public1.transition.live_snapshot.next_pair_index
      2#u32)
  let i11 ← lift (i10 &&& 1#u64)
  let digests7 ←
    if i11 = 0#u64
    then
      do
      let i12 ← lift (Std.Usize.wrapping_mul block2 16#usize)
      let q3 ← reference_copy_terminal.Selectors.row selectors i12
      let a ← reference_terminal.empty_root 2#usize
      reference_terminal.add_digest_binding output q3 openings.z
        aspis_statement.poseidon2.RATE a true
    else
      do
      let i12 ← lift (Std.Usize.wrapping_mul block2 16#usize)
      let i13 ← lift (Std.Usize.wrapping_add i12 12#usize)
      let q3 ← reference_copy_terminal.Selectors.row selectors i13
      let a ←
        reference_terminal.digest227 public1.transition.live_snapshot.frontier
          2#usize
      reference_terminal.add_digest_binding output q3 openings.z 0#usize a
        false
  digest_raw_07 public1 openings selectors digests7

theorem digest_head_06_factor (public1 : reference_terminal.SemanticPublic)
    (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
    (selectors : reference_copy_terminal.Selectors) (output : Digest8Q) :
    digest_raw_06 public1 openings selectors output = digest_head_06 public1 openings selectors output := by
  rfl

attribute [local irreducible] digest_raw_07

theorem digest_head_06_equation (public1 : reference_terminal.SemanticPublic)
    (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
    (selectors : reference_copy_terminal.Selectors) (output : Digest8Q) :
    digest_head_06 public1 openings selectors output = digest_stage_06 public1 openings selectors output >>= digest_raw_07 public1 openings selectors := by
  simp only [digest_head_06,digest_stage_06,digest_assoc,digest_if_bind,digest_option_bind]

theorem digest_raw_06_success (public1 : reference_terminal.SemanticPublic)
    (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
    (selectors : reference_copy_terminal.Selectors) (output : Digest8Q) :
    Success (digest_raw_06 public1 openings selectors output) := by
  rw [digest_head_06_factor,digest_head_06_equation]
  apply bind
  · exact digest_stage_06_success public1 openings selectors output
  intro next
  exact digest_raw_07_success public1 openings selectors next

#print axioms digest_head_06_factor
#print axioms digest_head_06_equation
#print axioms digest_raw_06_success

def digest_head_05 (public1 : reference_terminal.SemanticPublic)
    (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
    (selectors : reference_copy_terminal.Selectors) (output : Digest8Q) : Result Digest8Q := do
  let block1 ← lift (Std.Usize.wrapping_add 34#usize 1#usize)
  let i8 ←
    lift (Std.U64.wrapping_shr public1.transition.live_snapshot.next_pair_index
      1#u32)
  let i9 ← lift (i8 &&& 1#u64)
  let digests6 ←
    if i9 = 0#u64
    then
      do
      let i10 ← lift (Std.Usize.wrapping_mul block1 16#usize)
      let q3 ← reference_copy_terminal.Selectors.row selectors i10
      let a ← reference_terminal.empty_root 1#usize
      reference_terminal.add_digest_binding output q3 openings.z
        aspis_statement.poseidon2.RATE a true
    else
      do
      let i10 ← lift (Std.Usize.wrapping_mul block1 16#usize)
      let i11 ← lift (Std.Usize.wrapping_add i10 12#usize)
      let q3 ← reference_copy_terminal.Selectors.row selectors i11
      let a ←
        reference_terminal.digest227 public1.transition.live_snapshot.frontier
          1#usize
      reference_terminal.add_digest_binding output q3 openings.z 0#usize a
        false
  digest_raw_06 public1 openings selectors digests6

theorem digest_head_05_factor (public1 : reference_terminal.SemanticPublic)
    (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
    (selectors : reference_copy_terminal.Selectors) (output : Digest8Q) :
    digest_raw_05 public1 openings selectors output = digest_head_05 public1 openings selectors output := by
  rfl

attribute [local irreducible] digest_raw_06

theorem digest_head_05_equation (public1 : reference_terminal.SemanticPublic)
    (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
    (selectors : reference_copy_terminal.Selectors) (output : Digest8Q) :
    digest_head_05 public1 openings selectors output = digest_stage_05 public1 openings selectors output >>= digest_raw_06 public1 openings selectors := by
  simp only [digest_head_05,digest_stage_05,digest_assoc,digest_if_bind,digest_option_bind]

theorem digest_raw_05_success (public1 : reference_terminal.SemanticPublic)
    (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
    (selectors : reference_copy_terminal.Selectors) (output : Digest8Q) :
    Success (digest_raw_05 public1 openings selectors output) := by
  rw [digest_head_05_factor,digest_head_05_equation]
  apply bind
  · exact digest_stage_05_success public1 openings selectors output
  intro next
  exact digest_raw_06_success public1 openings selectors next

#print axioms digest_head_05_factor
#print axioms digest_head_05_equation
#print axioms digest_raw_05_success

def digest_head_04 (public1 : reference_terminal.SemanticPublic)
    (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
    (selectors : reference_copy_terminal.Selectors) (output : Digest8Q) : Result Digest8Q := do
  let block ← lift (Std.Usize.wrapping_add 34#usize 0#usize)
  let i6 ←
    lift (Std.U64.wrapping_shr public1.transition.live_snapshot.next_pair_index
      0#u32)
  let i7 ← lift (i6 &&& 1#u64)
  let digests5 ←
    if i7 = 0#u64
    then
      do
      let i8 ← lift (Std.Usize.wrapping_mul block 16#usize)
      let q3 ← reference_copy_terminal.Selectors.row selectors i8
      let a ← reference_terminal.empty_root 0#usize
      reference_terminal.add_digest_binding output q3 openings.z
        aspis_statement.poseidon2.RATE a true
    else
      do
      let i8 ← lift (Std.Usize.wrapping_mul block 16#usize)
      let i9 ← lift (Std.Usize.wrapping_add i8 12#usize)
      let q3 ← reference_copy_terminal.Selectors.row selectors i9
      let a ←
        reference_terminal.digest227 public1.transition.live_snapshot.frontier
          0#usize
      reference_terminal.add_digest_binding output q3 openings.z 0#usize a
        false
  digest_raw_05 public1 openings selectors digests5

theorem digest_head_04_factor (public1 : reference_terminal.SemanticPublic)
    (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
    (selectors : reference_copy_terminal.Selectors) (output : Digest8Q) :
    digest_raw_04 public1 openings selectors output = digest_head_04 public1 openings selectors output := by
  rfl

attribute [local irreducible] digest_raw_05

theorem digest_head_04_equation (public1 : reference_terminal.SemanticPublic)
    (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
    (selectors : reference_copy_terminal.Selectors) (output : Digest8Q) :
    digest_head_04 public1 openings selectors output = digest_stage_04 public1 openings selectors output >>= digest_raw_05 public1 openings selectors := by
  simp only [digest_head_04,digest_stage_04,digest_assoc,digest_if_bind,digest_option_bind]

theorem digest_raw_04_success (public1 : reference_terminal.SemanticPublic)
    (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
    (selectors : reference_copy_terminal.Selectors) (output : Digest8Q) :
    Success (digest_raw_04 public1 openings selectors output) := by
  rw [digest_head_04_factor,digest_head_04_equation]
  apply bind
  · exact digest_stage_04_success public1 openings selectors output
  intro next
  exact digest_raw_05_success public1 openings selectors next

#print axioms digest_head_04_factor
#print axioms digest_head_04_equation
#print axioms digest_raw_04_success

def digest_head_03 (public1 : reference_terminal.SemanticPublic)
    (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
    (selectors : reference_copy_terminal.Selectors) (output : Digest8Q) : Result Digest8Q := do
  let i4 ← lift (Std.Usize.wrapping_mul 32#usize 16#usize)
  let i5 ← lift (Std.Usize.wrapping_add i4 11#usize)
  let q2 ← reference_copy_terminal.Selectors.row selectors i5
  let digests4 ←
    reference_terminal.add_digest_binding output q2 openings.z 0#usize
      public1.change false
  digest_raw_04 public1 openings selectors digests4

theorem digest_head_03_factor (public1 : reference_terminal.SemanticPublic)
    (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
    (selectors : reference_copy_terminal.Selectors) (output : Digest8Q) :
    digest_raw_03 public1 openings selectors output = digest_head_03 public1 openings selectors output := by
  rfl

attribute [local irreducible] digest_raw_04

theorem digest_head_03_equation (public1 : reference_terminal.SemanticPublic)
    (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
    (selectors : reference_copy_terminal.Selectors) (output : Digest8Q) :
    digest_head_03 public1 openings selectors output = digest_stage_03 public1 openings selectors output >>= digest_raw_04 public1 openings selectors := by
  simp only [digest_head_03,digest_stage_03,digest_assoc,digest_if_bind,digest_option_bind]

theorem digest_raw_03_success (public1 : reference_terminal.SemanticPublic)
    (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
    (selectors : reference_copy_terminal.Selectors) (output : Digest8Q) :
    Success (digest_raw_03 public1 openings selectors output) := by
  rw [digest_head_03_factor,digest_head_03_equation]
  apply bind
  · exact digest_stage_03_success public1 openings selectors output
  intro next
  exact digest_raw_04_success public1 openings selectors next

#print axioms digest_head_03_factor
#print axioms digest_head_03_equation
#print axioms digest_raw_03_success

def digest_head_02 (public1 : reference_terminal.SemanticPublic)
    (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
    (selectors : reference_copy_terminal.Selectors) (output : Digest8Q) : Result Digest8Q := do
  let digests3 ←
    match public1.recipient with
    | none => Result.ok output
    | some recipient =>
      do
      let i4 ← lift (Std.Usize.wrapping_mul 29#usize 16#usize)
      let i5 ← lift (Std.Usize.wrapping_add i4 11#usize)
      let q2 ← reference_copy_terminal.Selectors.row selectors i5
      reference_terminal.add_digest_binding output q2 openings.z 0#usize
        recipient false
  digest_raw_03 public1 openings selectors digests3

theorem digest_head_02_factor (public1 : reference_terminal.SemanticPublic)
    (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
    (selectors : reference_copy_terminal.Selectors) (output : Digest8Q) :
    digest_raw_02 public1 openings selectors output = digest_head_02 public1 openings selectors output := by
  rfl

attribute [local irreducible] digest_raw_03

theorem digest_head_02_equation (public1 : reference_terminal.SemanticPublic)
    (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
    (selectors : reference_copy_terminal.Selectors) (output : Digest8Q) :
    digest_head_02 public1 openings selectors output = digest_stage_02 public1 openings selectors output >>= digest_raw_03 public1 openings selectors := by
  cases hr : public1.recipient <;>
    simp only [digest_head_02,digest_stage_02,hr,digest_assoc,bind_tc_ok]

theorem digest_raw_02_success (public1 : reference_terminal.SemanticPublic)
    (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
    (selectors : reference_copy_terminal.Selectors) (output : Digest8Q) :
    Success (digest_raw_02 public1 openings selectors output) := by
  rw [digest_head_02_factor,digest_head_02_equation]
  apply bind
  · exact digest_stage_02_success public1 openings selectors output
  intro next
  exact digest_raw_03_success public1 openings selectors next

#print axioms digest_head_02_factor
#print axioms digest_head_02_equation
#print axioms digest_raw_02_success

def digest_head_01 (public1 : reference_terminal.SemanticPublic)
    (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
    (selectors : reference_copy_terminal.Selectors) (output : Digest8Q) : Result Digest8Q := do
  let i2 ← lift (Std.Usize.wrapping_mul 26#usize 16#usize)
  let i3 ← lift (Std.Usize.wrapping_add i2 11#usize)
  let q1 ← reference_copy_terminal.Selectors.row selectors i3
  let digests2 ←
    reference_terminal.add_digest_binding output q1 openings.z 0#usize
      public1.nullifier false
  digest_raw_02 public1 openings selectors digests2

theorem digest_head_01_factor (public1 : reference_terminal.SemanticPublic)
    (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
    (selectors : reference_copy_terminal.Selectors) (output : Digest8Q) :
    digest_raw_01 public1 openings selectors output = digest_head_01 public1 openings selectors output := by
  rfl

attribute [local irreducible] digest_raw_02

theorem digest_head_01_equation (public1 : reference_terminal.SemanticPublic)
    (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
    (selectors : reference_copy_terminal.Selectors) (output : Digest8Q) :
    digest_head_01 public1 openings selectors output = digest_stage_01 public1 openings selectors output >>= digest_raw_02 public1 openings selectors := by
  simp only [digest_head_01,digest_stage_01,digest_assoc,digest_if_bind,digest_option_bind]

theorem digest_raw_01_success (public1 : reference_terminal.SemanticPublic)
    (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
    (selectors : reference_copy_terminal.Selectors) (output : Digest8Q) :
    Success (digest_raw_01 public1 openings selectors output) := by
  rw [digest_head_01_factor,digest_head_01_equation]
  apply bind
  · exact digest_stage_01_success public1 openings selectors output
  intro next
  exact digest_raw_02_success public1 openings selectors next

#print axioms digest_head_01_factor
#print axioms digest_head_01_equation
#print axioms digest_raw_01_success

attribute [local irreducible] digest_raw_01

theorem digest_head_00_equation (public1 : reference_terminal.SemanticPublic)
    (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
    (selectors : reference_copy_terminal.Selectors) :
    digest_head_00 public1 openings selectors = digest_stage_00 public1 openings selectors >>= digest_raw_01 public1 openings selectors := by
  simp only [digest_head_00,digest_stage_00,digest_assoc,digest_if_bind,digest_option_bind]

theorem digest_raw_00_success (public1 : reference_terminal.SemanticPublic)
    (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
    (selectors : reference_copy_terminal.Selectors) :
    Success (reference_terminal.public_digest_lanes public1 openings selectors) := by
  rw [digest_head_00_factor,digest_head_00_equation]
  apply bind
  · exact digest_stage_00_success public1 openings selectors
  intro next
  exact digest_raw_01_success public1 openings selectors next

#print axioms digest_head_00_equation
#print axioms digest_raw_00_success

theorem public_digest_success8 (p : reference_terminal.SemanticPublic)
    (o : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
    (s : reference_copy_terminal.Selectors) :
    Success (reference_terminal.public_digest_lanes p o s) :=
  digest_raw_00_success p o s
#print axioms public_digest_success8
end PV_B3P_Success227
