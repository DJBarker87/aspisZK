import PV_B3P_BytesTypes226
open Aeneas Aeneas.Std Result ControlFlow Error
set_option maxRecDepth 2048
set_option maxHeartbeats 1000000
namespace PV_B3P_226
def reference226.project_frontier_level
  (out : reference226.OwnedPublic)
  (transition :
  aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementV1)
  (level : Std.Usize) :
  Result reference226.OwnedPublic
  := do
  let a ← Array.index_usize transition.live_snapshot.frontier level
  let m ← Array.index_usize a 0#usize
  let (a1, index_mut_back) ← Array.index_mut_usize out.frontier level
  let a2 ← Array.update a1 0#usize m
  let a3 ←
    Array.index_usize transition.candidate_afterstate.next_frontier level
  let m1 ← Array.index_usize a3 0#usize
  let (a4, index_mut_back1) ← Array.index_mut_usize out.next_frontier level
  let a5 ← Array.update a4 0#usize m1
  let m2 ← Array.index_usize a 1#usize
  let a6 := index_mut_back a2
  let (a7, index_mut_back2) ← Array.index_mut_usize a6 level
  let a8 ← Array.update a7 1#usize m2
  let m3 ← Array.index_usize a3 1#usize
  let a9 := index_mut_back1 a5
  let (a10, index_mut_back3) ← Array.index_mut_usize a9 level
  let a11 ← Array.update a10 1#usize m3
  let m4 ← Array.index_usize a 2#usize
  let a12 := index_mut_back2 a8
  let (a13, index_mut_back4) ← Array.index_mut_usize a12 level
  let a14 ← Array.update a13 2#usize m4
  let m5 ← Array.index_usize a3 2#usize
  let a15 := index_mut_back3 a11
  let (a16, index_mut_back5) ← Array.index_mut_usize a15 level
  let a17 ← Array.update a16 2#usize m5
  let m6 ← Array.index_usize a 3#usize
  let a18 := index_mut_back4 a14
  let (a19, index_mut_back6) ← Array.index_mut_usize a18 level
  let a20 ← Array.update a19 3#usize m6
  let m7 ← Array.index_usize a3 3#usize
  let a21 := index_mut_back5 a17
  let (a22, index_mut_back7) ← Array.index_mut_usize a21 level
  let a23 ← Array.update a22 3#usize m7
  let m8 ← Array.index_usize a 4#usize
  let a24 := index_mut_back6 a20
  let (a25, index_mut_back8) ← Array.index_mut_usize a24 level
  let a26 ← Array.update a25 4#usize m8
  let m9 ← Array.index_usize a3 4#usize
  let a27 := index_mut_back7 a23
  let (a28, index_mut_back9) ← Array.index_mut_usize a27 level
  let a29 ← Array.update a28 4#usize m9
  let m10 ← Array.index_usize a 5#usize
  let a30 := index_mut_back8 a26
  let (a31, index_mut_back10) ← Array.index_mut_usize a30 level
  let a32 ← Array.update a31 5#usize m10
  let m11 ← Array.index_usize a3 5#usize
  let a33 := index_mut_back9 a29
  let (a34, index_mut_back11) ← Array.index_mut_usize a33 level
  let a35 ← Array.update a34 5#usize m11
  let m12 ← Array.index_usize a 6#usize
  let a36 := index_mut_back10 a32
  let (a37, index_mut_back12) ← Array.index_mut_usize a36 level
  let a38 ← Array.update a37 6#usize m12
  let m13 ← Array.index_usize a3 6#usize
  let a39 := index_mut_back11 a35
  let (a40, index_mut_back13) ← Array.index_mut_usize a39 level
  let a41 ← Array.update a40 6#usize m13
  let m14 ← Array.index_usize a 7#usize
  let a42 := index_mut_back12 a38
  let (a43, index_mut_back14) ← Array.index_mut_usize a42 level
  let a44 ← Array.update a43 7#usize m14
  let m15 ← Array.index_usize a3 7#usize
  let a45 := index_mut_back13 a41
  let (a46, index_mut_back15) ← Array.index_mut_usize a45 level
  let a47 ← Array.update a46 7#usize m15
  let a48 := index_mut_back14 a44
  let a49 := index_mut_back15 a47
  ok { out with frontier := a48, next_frontier := a49 }


end PV_B3P_226
#print axioms PV_B3P_226.reference226.project_frontier_level
