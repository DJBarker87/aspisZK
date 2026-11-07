import NMT_R2_ResultTry
import NMT_345PrefixFold
set_option autoImplicit false
noncomputable section
namespace NMT_R2_PrefixPacket
open Aeneas Aeneas.Std NMT_345 NMT_R2_ResultTry

def packPrefix {W : Type} (c : Calls) (s : Selected W) : R (Decoded W) :=
 NMT_R2_ResultTry.bind (c.c15 (selectedArray s)) fun _ =>
 NMT_R2_ResultTry.bind (c.c13 s.proofAccount) fun _ =>
 NMT_R2_ResultTry.bind (c.c13 s.publicAccount) fun _ =>
 NMT_R2_ResultTry.bind (c.c14 s.checkpointAccount s.program true) fun _ =>
 NMT_R2_ResultTry.bind (NMT_stage1_owned.r1_pool_adapter.owned.OwnedAccount.data c.c10 s.checkpointAccount) fun ck =>
 NMT_R2_ResultTry.bind (c.c16 ck) fun _ =>
 NMT_R2_ResultTry.bind (NMT_stage1_owned.r1_pool_adapter.owned.OwnedAccount.data c.c10 s.publicAccount) fun pub =>
 NMT_R2_ResultTry.bind (c.c12 pub) fun statement => NMT_R2_ResultTry.pure ⟨⟨⟨s,ck⟩,pub⟩,statement⟩

/-- A phase-only association of the already checked source occurrences. The
packet carries the original parent and exact child arguments, no erasure. -/
theorem source {W : Type} (c : Calls) (s : Selected W) (next : Decoded W → Result Ret) :
 NMT_R2_ResultTry.bind (packPrefix c s) next = prefixFold c s next := by
 simp only [packPrefix,NMT_R2_ResultTry.assoc,NMT_R2_ResultTry.pure_left]
 rfl
#print axioms source
end NMT_R2_PrefixPacket
end
