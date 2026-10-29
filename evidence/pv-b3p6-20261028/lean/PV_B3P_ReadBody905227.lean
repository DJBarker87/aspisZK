import PV_B3P_P227_11
import PV_B3P_ReadFunctions9227
namespace PV_B3P_Binding9227
open Aeneas Aeneas.Std PV_B3P_227 Result ControlFlow Error
set_option autoImplicit false

/-- Exact emitted body context; only the immutable-read callee is abstracted. -/
def reference_terminal_public_digest_lanes_read_context9 (source_read : (Array (Array U32 8#usize) 20#usize → Usize → Result (Array U32 8#usize))) (public1 : reference_terminal.SemanticPublic)
  (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
  (selectors : reference_copy_terminal.Selectors)  :
  Result (Array aspis_core.field.QM31 8#usize) :=  do
  let digests := Array.repeat 8#usize aspis_core.field.QM31.ZERO
  let i ← lift (Std.Usize.wrapping_mul 56#usize 16#usize)
  let i1 ← lift (Std.Usize.wrapping_add i 11#usize)
  let q ← reference_copy_terminal.Selectors.row selectors i1
  let digests1 ←
    reference_terminal.add_digest_binding digests q openings.z 0#usize
      public1.anchor false
  let i2 ← lift (Std.Usize.wrapping_mul 26#usize 16#usize)
  let i3 ← lift (Std.Usize.wrapping_add i2 11#usize)
  let q1 ← reference_copy_terminal.Selectors.row selectors i3
  let digests2 ←
    reference_terminal.add_digest_binding digests1 q1 openings.z 0#usize
      public1.nullifier false
  let digests3 ←
    match public1.recipient with
    | none => ok digests2
    | some recipient =>
      do
      let i4 ← lift (Std.Usize.wrapping_mul 29#usize 16#usize)
      let i5 ← lift (Std.Usize.wrapping_add i4 11#usize)
      let q2 ← reference_copy_terminal.Selectors.row selectors i5
      reference_terminal.add_digest_binding digests2 q2 openings.z 0#usize
        recipient false
  let i4 ← lift (Std.Usize.wrapping_mul 32#usize 16#usize)
  let i5 ← lift (Std.Usize.wrapping_add i4 11#usize)
  let q2 ← reference_copy_terminal.Selectors.row selectors i5
  let digests4 ←
    reference_terminal.add_digest_binding digests3 q2 openings.z 0#usize
      public1.change false
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
      reference_terminal.add_digest_binding digests4 q3 openings.z
        aspis_statement.poseidon2.RATE a true
    else
      do
      let i8 ← lift (Std.Usize.wrapping_mul block 16#usize)
      let i9 ← lift (Std.Usize.wrapping_add i8 12#usize)
      let q3 ← reference_copy_terminal.Selectors.row selectors i9
      let a ←
        source_read public1.transition.live_snapshot.frontier
          0#usize
      reference_terminal.add_digest_binding digests4 q3 openings.z 0#usize a
        false
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
      reference_terminal.add_digest_binding digests5 q3 openings.z
        aspis_statement.poseidon2.RATE a true
    else
      do
      let i10 ← lift (Std.Usize.wrapping_mul block1 16#usize)
      let i11 ← lift (Std.Usize.wrapping_add i10 12#usize)
      let q3 ← reference_copy_terminal.Selectors.row selectors i11
      let a ←
        source_read public1.transition.live_snapshot.frontier
          1#usize
      reference_terminal.add_digest_binding digests5 q3 openings.z 0#usize a
        false
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
      reference_terminal.add_digest_binding digests6 q3 openings.z
        aspis_statement.poseidon2.RATE a true
    else
      do
      let i12 ← lift (Std.Usize.wrapping_mul block2 16#usize)
      let i13 ← lift (Std.Usize.wrapping_add i12 12#usize)
      let q3 ← reference_copy_terminal.Selectors.row selectors i13
      let a ←
        source_read public1.transition.live_snapshot.frontier
          2#usize
      reference_terminal.add_digest_binding digests6 q3 openings.z 0#usize a
        false
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
      reference_terminal.add_digest_binding digests7 q3 openings.z
        aspis_statement.poseidon2.RATE a true
    else
      do
      let i14 ← lift (Std.Usize.wrapping_mul block3 16#usize)
      let i15 ← lift (Std.Usize.wrapping_add i14 12#usize)
      let q3 ← reference_copy_terminal.Selectors.row selectors i15
      let a ←
        source_read public1.transition.live_snapshot.frontier
          3#usize
      reference_terminal.add_digest_binding digests7 q3 openings.z 0#usize a
        false
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
      reference_terminal.add_digest_binding digests8 q3 openings.z
        aspis_statement.poseidon2.RATE a true
    else
      do
      let i16 ← lift (Std.Usize.wrapping_mul block4 16#usize)
      let i17 ← lift (Std.Usize.wrapping_add i16 12#usize)
      let q3 ← reference_copy_terminal.Selectors.row selectors i17
      let a ←
        source_read public1.transition.live_snapshot.frontier
          4#usize
      reference_terminal.add_digest_binding digests8 q3 openings.z 0#usize a
        false
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
      reference_terminal.add_digest_binding digests9 q3 openings.z
        aspis_statement.poseidon2.RATE a true
    else
      do
      let i18 ← lift (Std.Usize.wrapping_mul block5 16#usize)
      let i19 ← lift (Std.Usize.wrapping_add i18 12#usize)
      let q3 ← reference_copy_terminal.Selectors.row selectors i19
      let a ←
        source_read public1.transition.live_snapshot.frontier
          5#usize
      reference_terminal.add_digest_binding digests9 q3 openings.z 0#usize a
        false
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
      reference_terminal.add_digest_binding digests10 q3 openings.z
        aspis_statement.poseidon2.RATE a true
    else
      do
      let i20 ← lift (Std.Usize.wrapping_mul block6 16#usize)
      let i21 ← lift (Std.Usize.wrapping_add i20 12#usize)
      let q3 ← reference_copy_terminal.Selectors.row selectors i21
      let a ←
        source_read public1.transition.live_snapshot.frontier
          6#usize
      reference_terminal.add_digest_binding digests10 q3 openings.z 0#usize a
        false
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
      reference_terminal.add_digest_binding digests11 q3 openings.z
        aspis_statement.poseidon2.RATE a true
    else
      do
      let i22 ← lift (Std.Usize.wrapping_mul block7 16#usize)
      let i23 ← lift (Std.Usize.wrapping_add i22 12#usize)
      let q3 ← reference_copy_terminal.Selectors.row selectors i23
      let a ←
        source_read public1.transition.live_snapshot.frontier
          7#usize
      reference_terminal.add_digest_binding digests11 q3 openings.z 0#usize a
        false
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
      reference_terminal.add_digest_binding digests12 q3 openings.z
        aspis_statement.poseidon2.RATE a true
    else
      do
      let i24 ← lift (Std.Usize.wrapping_mul block8 16#usize)
      let i25 ← lift (Std.Usize.wrapping_add i24 12#usize)
      let q3 ← reference_copy_terminal.Selectors.row selectors i25
      let a ←
        source_read public1.transition.live_snapshot.frontier
          8#usize
      reference_terminal.add_digest_binding digests12 q3 openings.z 0#usize a
        false
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
      reference_terminal.add_digest_binding digests13 q3 openings.z
        aspis_statement.poseidon2.RATE a true
    else
      do
      let i26 ← lift (Std.Usize.wrapping_mul block9 16#usize)
      let i27 ← lift (Std.Usize.wrapping_add i26 12#usize)
      let q3 ← reference_copy_terminal.Selectors.row selectors i27
      let a ←
        source_read public1.transition.live_snapshot.frontier
          9#usize
      reference_terminal.add_digest_binding digests13 q3 openings.z 0#usize a
        false
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
      reference_terminal.add_digest_binding digests14 q3 openings.z
        aspis_statement.poseidon2.RATE a true
    else
      do
      let i28 ← lift (Std.Usize.wrapping_mul block10 16#usize)
      let i29 ← lift (Std.Usize.wrapping_add i28 12#usize)
      let q3 ← reference_copy_terminal.Selectors.row selectors i29
      let a ←
        source_read public1.transition.live_snapshot.frontier
          10#usize
      reference_terminal.add_digest_binding digests14 q3 openings.z 0#usize a
        false
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
      reference_terminal.add_digest_binding digests15 q3 openings.z
        aspis_statement.poseidon2.RATE a true
    else
      do
      let i30 ← lift (Std.Usize.wrapping_mul block11 16#usize)
      let i31 ← lift (Std.Usize.wrapping_add i30 12#usize)
      let q3 ← reference_copy_terminal.Selectors.row selectors i31
      let a ←
        source_read public1.transition.live_snapshot.frontier
          11#usize
      reference_terminal.add_digest_binding digests15 q3 openings.z 0#usize a
        false
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
      reference_terminal.add_digest_binding digests16 q3 openings.z
        aspis_statement.poseidon2.RATE a true
    else
      do
      let i32 ← lift (Std.Usize.wrapping_mul block12 16#usize)
      let i33 ← lift (Std.Usize.wrapping_add i32 12#usize)
      let q3 ← reference_copy_terminal.Selectors.row selectors i33
      let a ←
        source_read public1.transition.live_snapshot.frontier
          12#usize
      reference_terminal.add_digest_binding digests16 q3 openings.z 0#usize a
        false
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
      reference_terminal.add_digest_binding digests17 q3 openings.z
        aspis_statement.poseidon2.RATE a true
    else
      do
      let i34 ← lift (Std.Usize.wrapping_mul block13 16#usize)
      let i35 ← lift (Std.Usize.wrapping_add i34 12#usize)
      let q3 ← reference_copy_terminal.Selectors.row selectors i35
      let a ←
        source_read public1.transition.live_snapshot.frontier
          13#usize
      reference_terminal.add_digest_binding digests17 q3 openings.z 0#usize a
        false
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
      reference_terminal.add_digest_binding digests18 q3 openings.z
        aspis_statement.poseidon2.RATE a true
    else
      do
      let i36 ← lift (Std.Usize.wrapping_mul block14 16#usize)
      let i37 ← lift (Std.Usize.wrapping_add i36 12#usize)
      let q3 ← reference_copy_terminal.Selectors.row selectors i37
      let a ←
        source_read public1.transition.live_snapshot.frontier
          14#usize
      reference_terminal.add_digest_binding digests18 q3 openings.z 0#usize a
        false
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
      reference_terminal.add_digest_binding digests19 q3 openings.z
        aspis_statement.poseidon2.RATE a true
    else
      do
      let i38 ← lift (Std.Usize.wrapping_mul block15 16#usize)
      let i39 ← lift (Std.Usize.wrapping_add i38 12#usize)
      let q3 ← reference_copy_terminal.Selectors.row selectors i39
      let a ←
        source_read public1.transition.live_snapshot.frontier
          15#usize
      reference_terminal.add_digest_binding digests19 q3 openings.z 0#usize a
        false
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
      reference_terminal.add_digest_binding digests20 q3 openings.z
        aspis_statement.poseidon2.RATE a true
    else
      do
      let i40 ← lift (Std.Usize.wrapping_mul block16 16#usize)
      let i41 ← lift (Std.Usize.wrapping_add i40 12#usize)
      let q3 ← reference_copy_terminal.Selectors.row selectors i41
      let a ←
        source_read public1.transition.live_snapshot.frontier
          16#usize
      reference_terminal.add_digest_binding digests20 q3 openings.z 0#usize a
        false
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
      reference_terminal.add_digest_binding digests21 q3 openings.z
        aspis_statement.poseidon2.RATE a true
    else
      do
      let i42 ← lift (Std.Usize.wrapping_mul block17 16#usize)
      let i43 ← lift (Std.Usize.wrapping_add i42 12#usize)
      let q3 ← reference_copy_terminal.Selectors.row selectors i43
      let a ←
        source_read public1.transition.live_snapshot.frontier
          17#usize
      reference_terminal.add_digest_binding digests21 q3 openings.z 0#usize a
        false
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
      reference_terminal.add_digest_binding digests22 q3 openings.z
        aspis_statement.poseidon2.RATE a true
    else
      do
      let i44 ← lift (Std.Usize.wrapping_mul block18 16#usize)
      let i45 ← lift (Std.Usize.wrapping_add i44 12#usize)
      let q3 ← reference_copy_terminal.Selectors.row selectors i45
      let a ←
        source_read public1.transition.live_snapshot.frontier
          18#usize
      reference_terminal.add_digest_binding digests22 q3 openings.z 0#usize a
        false
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
      reference_terminal.add_digest_binding digests23 q3 openings.z
        aspis_statement.poseidon2.RATE a true
    else
      do
      let i46 ← lift (Std.Usize.wrapping_mul block19 16#usize)
      let i47 ← lift (Std.Usize.wrapping_add i46 12#usize)
      let q3 ← reference_copy_terminal.Selectors.row selectors i47
      let a ←
        source_read public1.transition.live_snapshot.frontier
          19#usize
      reference_terminal.add_digest_binding digests23 q3 openings.z 0#usize a
        false
  let i46 ← lift (Std.Usize.wrapping_mul 53#usize 16#usize)
  let i47 ← lift (Std.Usize.wrapping_add i46 11#usize)
  let q3 ← reference_copy_terminal.Selectors.row selectors i47
  let digests25 ←
    reference_terminal.add_digest_binding digests24 q3 openings.z 0#usize
      public1.transition.candidate_afterstate.next_root false
  let carry ←
    reference_terminal.bounded_append_carry
      public1.transition.live_snapshot.next_pair_index
  if carry < 20#usize
  then
    let i48 ← lift (Std.Usize.wrapping_add 33#usize carry)
    let i49 ← lift (Std.Usize.wrapping_mul i48 16#usize)
    let i50 ← lift (Std.Usize.wrapping_add i49 11#usize)
    let q4 ← reference_copy_terminal.Selectors.row selectors i50
    let a ←
      Array.index_usize public1.transition.candidate_afterstate.next_frontier
        carry
    reference_terminal.add_digest_binding digests25 q4 openings.z 0#usize a
      false
  else ok digests25

def reference_terminal_public_digest_lanes_direct_read9 (public1 : reference_terminal.SemanticPublic)
  (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
  (selectors : reference_copy_terminal.Selectors)  :
  Result (Array aspis_core.field.QM31 8#usize) :=
  reference_terminal_public_digest_lanes_read_context9 (fun values i => Array.index_usize values i) public1 openings selectors

theorem reference_terminal_public_digest_lanes_read_binding9 (public1 : reference_terminal.SemanticPublic)
  (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
  (selectors : reference_copy_terminal.Selectors)  :
    reference_terminal.public_digest_lanes public1 openings selectors = reference_terminal_public_digest_lanes_direct_read9 public1 openings selectors :=
  congrArg (fun source_read => reference_terminal_public_digest_lanes_read_context9 source_read public1 openings selectors) digest_function_binding

#print axioms reference_terminal_public_digest_lanes_read_binding9
end PV_B3P_Binding9227
