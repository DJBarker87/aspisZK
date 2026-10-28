import PV_B3P_ByteProjectLevel226
open Aeneas Aeneas.Std Result ControlFlow Error
set_option maxRecDepth 2048
set_option maxHeartbeats 1000000
namespace PV_B3P_226
def reference226.project
  (public1 : reference226.Source) : Result reference226.OwnedPublic := do
  let (withdrawal, anchor, nullifier, asset_id, recipient, change,
    withdrawal_amount, transition) ←
    match public1 with
    | reference226.Source.Transfer p t =>
      ok (false, p.anchor_root, p.nullifier, p.asset_id,
        p.recipient_commitment, p.change_commitment, 0#u32, t)
    | reference226.Source.Withdrawal p t =>
      let a := Array.repeat 8#usize aspis_core.field.M31.ZERO
      ok (true, p.anchor_root, p.nullifier, p.asset_id, a, p.change_commitment,
        p.amount, t)
  let a := Array.repeat 8#usize 0#u32
  let a1 := Array.repeat 8#usize 0#u32
  let a2 := Array.repeat 8#usize 0#u32
  let a3 := Array.repeat 8#usize 0#u32
  let a4 := Array.repeat 8#usize 0#u32
  let a5 := Array.repeat 20#usize a4
  let a6 := Array.repeat 8#usize 0#u32
  let a7 := Array.repeat 8#usize 0#u32
  let a8 := Array.repeat 20#usize a7
  let m ← Array.index_usize anchor 0#usize
  let a9 ← Array.update a 0#usize m
  let m1 ← Array.index_usize nullifier 0#usize
  let a10 ← Array.update a1 0#usize m1
  let m2 ← Array.index_usize recipient 0#usize
  let a11 ← Array.update a2 0#usize m2
  let m3 ← Array.index_usize change 0#usize
  let a12 ← Array.update a3 0#usize m3
  let m4 ←
    Array.index_usize transition.candidate_afterstate.next_root 0#usize
  let a13 ← Array.update a6 0#usize m4
  let m5 ← Array.index_usize anchor 1#usize
  let a14 ← Array.update a9 1#usize m5
  let m6 ← Array.index_usize nullifier 1#usize
  let a15 ← Array.update a10 1#usize m6
  let m7 ← Array.index_usize recipient 1#usize
  let a16 ← Array.update a11 1#usize m7
  let m8 ← Array.index_usize change 1#usize
  let a17 ← Array.update a12 1#usize m8
  let m9 ←
    Array.index_usize transition.candidate_afterstate.next_root 1#usize
  let a18 ← Array.update a13 1#usize m9
  let m10 ← Array.index_usize anchor 2#usize
  let a19 ← Array.update a14 2#usize m10
  let m11 ← Array.index_usize nullifier 2#usize
  let a20 ← Array.update a15 2#usize m11
  let m12 ← Array.index_usize recipient 2#usize
  let a21 ← Array.update a16 2#usize m12
  let m13 ← Array.index_usize change 2#usize
  let a22 ← Array.update a17 2#usize m13
  let m14 ←
    Array.index_usize transition.candidate_afterstate.next_root 2#usize
  let a23 ← Array.update a18 2#usize m14
  let m15 ← Array.index_usize anchor 3#usize
  let a24 ← Array.update a19 3#usize m15
  let m16 ← Array.index_usize nullifier 3#usize
  let a25 ← Array.update a20 3#usize m16
  let m17 ← Array.index_usize recipient 3#usize
  let a26 ← Array.update a21 3#usize m17
  let m18 ← Array.index_usize change 3#usize
  let a27 ← Array.update a22 3#usize m18
  let m19 ←
    Array.index_usize transition.candidate_afterstate.next_root 3#usize
  let a28 ← Array.update a23 3#usize m19
  let m20 ← Array.index_usize anchor 4#usize
  let a29 ← Array.update a24 4#usize m20
  let m21 ← Array.index_usize nullifier 4#usize
  let a30 ← Array.update a25 4#usize m21
  let m22 ← Array.index_usize recipient 4#usize
  let a31 ← Array.update a26 4#usize m22
  let m23 ← Array.index_usize change 4#usize
  let a32 ← Array.update a27 4#usize m23
  let m24 ←
    Array.index_usize transition.candidate_afterstate.next_root 4#usize
  let a33 ← Array.update a28 4#usize m24
  let m25 ← Array.index_usize anchor 5#usize
  let a34 ← Array.update a29 5#usize m25
  let m26 ← Array.index_usize nullifier 5#usize
  let a35 ← Array.update a30 5#usize m26
  let m27 ← Array.index_usize recipient 5#usize
  let a36 ← Array.update a31 5#usize m27
  let m28 ← Array.index_usize change 5#usize
  let a37 ← Array.update a32 5#usize m28
  let m29 ←
    Array.index_usize transition.candidate_afterstate.next_root 5#usize
  let a38 ← Array.update a33 5#usize m29
  let m30 ← Array.index_usize anchor 6#usize
  let a39 ← Array.update a34 6#usize m30
  let m31 ← Array.index_usize nullifier 6#usize
  let a40 ← Array.update a35 6#usize m31
  let m32 ← Array.index_usize recipient 6#usize
  let a41 ← Array.update a36 6#usize m32
  let m33 ← Array.index_usize change 6#usize
  let a42 ← Array.update a37 6#usize m33
  let m34 ←
    Array.index_usize transition.candidate_afterstate.next_root 6#usize
  let a43 ← Array.update a38 6#usize m34
  let m35 ← Array.index_usize anchor 7#usize
  let a44 ← Array.update a39 7#usize m35
  let m36 ← Array.index_usize nullifier 7#usize
  let a45 ← Array.update a40 7#usize m36
  let m37 ← Array.index_usize recipient 7#usize
  let a46 ← Array.update a41 7#usize m37
  let m38 ← Array.index_usize change 7#usize
  let a47 ← Array.update a42 7#usize m38
  let m39 ←
    Array.index_usize transition.candidate_afterstate.next_root 7#usize
  let a48 ← Array.update a43 7#usize m39
  let out ←
    reference226.project_frontier_level
      {
        withdrawal,
        anchor := a44,
        nullifier := a45,
        asset_id,
        recipient := a46,
        change := a47,
        withdrawal_amount,
        next_pair_index := transition.live_snapshot.next_pair_index,
        frontier := a5,
        next_root := a48,
        next_frontier := a8
      } transition 0#usize
  let out1 ← reference226.project_frontier_level out transition 1#usize
  let out2 ← reference226.project_frontier_level out1 transition 2#usize
  let out3 ← reference226.project_frontier_level out2 transition 3#usize
  let out4 ← reference226.project_frontier_level out3 transition 4#usize
  let out5 ← reference226.project_frontier_level out4 transition 5#usize
  let out6 ← reference226.project_frontier_level out5 transition 6#usize
  let out7 ← reference226.project_frontier_level out6 transition 7#usize
  let out8 ← reference226.project_frontier_level out7 transition 8#usize
  let out9 ← reference226.project_frontier_level out8 transition 9#usize
  let out10 ← reference226.project_frontier_level out9 transition 10#usize
  let out11 ← reference226.project_frontier_level out10 transition 11#usize
  let out12 ← reference226.project_frontier_level out11 transition 12#usize
  let out13 ← reference226.project_frontier_level out12 transition 13#usize
  let out14 ← reference226.project_frontier_level out13 transition 14#usize
  let out15 ← reference226.project_frontier_level out14 transition 15#usize
  let out16 ← reference226.project_frontier_level out15 transition 16#usize
  let out17 ← reference226.project_frontier_level out16 transition 17#usize
  let out18 ← reference226.project_frontier_level out17 transition 18#usize
  reference226.project_frontier_level out18 transition 19#usize


end PV_B3P_226
#print axioms PV_B3P_226.reference226.project
