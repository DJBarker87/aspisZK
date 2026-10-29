import R1Z.PV_OWNJ_FiatShamir
set_option autoImplicit false
namespace R1Z.PV_OWNJ_Causality
open PV_OWNJ_FiatShamir

/-- Every earlier challenge is reconstructed using only frames already
published before the next callback. Future records do not influence it. -/
theorem published_prefix (hash : Hash) (sample : Bytes → PV_OWNI_RawOps.Q)
 (statementBytes c1 : Bytes) (frames future : List Bytes) :
 (challenges hash sample statementBytes c1 (frames ++ future)).take frames.length =
 challenges hash sample statementBytes c1 frames := by
 unfold challenges
 rw [replay_append]
 simp only
 rw [← replay_length hash sample frames (seed hash statementBytes c1) 0]
 exact List.take_left

/-- A query observes only the preceding-round prior of the challenge list. -/
theorem query_prefix (sampleValue : Nat → PV_OWNI_RawOps.Q)
 (a b : List PV_OWNI_RawOps.Q) (round index assignment : Nat)
 (h : a.take round = b.take round) :
 query sampleValue a round index assignment = query sampleValue b round index assignment := by
 unfold query
 rw [h]

#print axioms published_prefix
#print axioms query_prefix
end R1Z.PV_OWNJ_Causality
