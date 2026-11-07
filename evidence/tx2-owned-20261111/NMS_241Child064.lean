import NMS_241Domain
import NMS_241OwnInstall
set_option autoImplicit false
noncomputable section
namespace NMS_241Child064
open Aeneas Aeneas.Std AdapterRw AspisR1
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
/-- Installs the CANDIDATE064 packet at the SAME local source arguments.
All call/range equations are LOCAL cut observations; this theorem is not a241
row root and they are never exported as own-input clauses. Only original
checkpoint bytes/Root0 remain in the recorded241 input Domain. -/
theorem install {Ambient X : Type} (H : Bytes → State)
 (digest : VTop_Stages.aspis_core.digest.Digest32 X) (hash : X)
 (ops : Ops) (accounts : NMS_241OwnClauses.Accounts)
 (own : NMS_241OwnClauses.Domain accounts)
 (before : NLM_PacketTypes.World Ambient)
 (proofAccount checkpointAccount : r1_pool_adapter.owned.OwnedAccount)
 (proofData proof checkpoint : Slice U8) (publicBytes : Array U8 1880#usize)
 (length start end_ : Usize)
 (proofIndexed : Slice.index_usize accounts 0#usize = .ok proofAccount)
 (checkpointIndexed : Slice.index_usize accounts 6#usize = .ok checkpointAccount)
 (proofRead : NMS_Emitted.get ops proofAccount = .ok (.Ok proofData))
 (checkpointRead : NMS_Emitted.get ops checkpointAccount = .ok (.Ok checkpoint))
 (validatedLength : length = 57607#usize)
 (startCall : aspis_statement.pool_v1.pair_terminal.POOL_V1_PAIR_VERIFIED_AFTERSTATE_BYTES ops = .ok start)
 (checked : Usize.checked_add start length = some end_)
 (guard : (Slice.len proofData != end_) = false)
 (range : core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
  proofData {start := start, «end» := end_} = .ok proof) :
 NMN_064.RowSpec H (NLW_Full064.Frame.mk
  (NLW_Full064.Args.mk digest publicBytes.to_slice proof checkpoint hash) before) := by
 rw [NLW_StartScope.proof_start ops] at startCall
 cases startCall
 have extent := NMS_241OwnInstall.checkpoint ops accounts own.1 checkpointAccount checkpoint
  checkpointIndexed checkpointRead
 have endSame := NLM_CheckedAddFacts.guard_eq proofData end_ guard
 have ownRange : core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
  proofData {start := 688#usize, «end» := Slice.len proofData} = .ok proof := by
  rw [endSame]
  exact range
 have root0 := NMS_241OwnInstall.root0 ops accounts own.2 proofAccount checkpointAccount
  proofData checkpoint proof proofIndexed checkpointIndexed proofRead checkpointRead ownRange
 exact NMN_064.root H _ (NMS_241Domain.from_entered digest hash proofData proof checkpoint
  publicBytes length end_ validatedLength checked guard range extent root0)
#print install
#print axioms install
end NMS_241Child064
