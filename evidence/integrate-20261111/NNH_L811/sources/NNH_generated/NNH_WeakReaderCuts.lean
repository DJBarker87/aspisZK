import NNH_WeakTx2Inputs
import NNH_SliceRangeOk
import NNC_WeakReader
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNH_WeakReaderCuts
open Aeneas Aeneas.Std Result NND_Carrier NNH_ModelCarrier _root_.AdapterRw
open S2W_NativeConsolidation S2W_ExtractionBoundary
open MultiproofConeCanonical
structure Facts (ops : _root_.AdapterRw.Ops) (id : Program)
 (xs : Accounts) (data : Slice U8) (clock : Slot) (s : SecondCut) : Prop where
 proofIndex : Slice.index_usize xs 0#usize = .ok s.proofAccount
 checkpointIndex : Slice.index_usize xs 6#usize = .ok s.checkpointAccount
 proofRead : _root_.AdapterRw.r1_pool_adapter.owned.OwnedAccount.data ops s.proofAccount = .ok (.Ok s.raw)
 checkpointRead : _root_.AdapterRw.r1_pool_adapter.owned.OwnedAccount.data ops s.checkpointAccount = .ok (.Ok s.checkpoint)
 range : core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
  s.raw ⟨688#usize,s.finish⟩ = .ok s.proof
 length : s.raw.val.length = s.finish.val
 suffix : bytesOf s.raw.val = (bytesOf s.raw.val).take 688 ++ bytesOf s.proof.val
 origin : P2P_Origin.Fact ops id xs data clock s
 proof_eq : bytes s.proof = RSL.slice (bytes s.raw) 688 58295

theorem produce (m : IDa_Deployed.Uninstalled NFN_NEW_GeometryDictionary.CE)
 (env : RSL.Env) (err : NFN_NEW_GeometryDictionary.CE) (r : NP6_StdModel.Reservation)
 (V : RSL.TX2_241.V2Lib) (program : solana_pubkey.Pubkey)
 (xs : Slice _root_.AdapterRw.r1_pool_adapter.owned.OwnedAccount) (data : Slice U8) (clock : Slot)
 (p : NNH_WeakTx2Inputs.Packet m env err r V program xs data clock) :
 ∃ s : SecondCut, Facts (NNH_CorrectConfiguration.sdk m env err r) program xs data clock s ∧
 s.raw = p.proof ∧ s.checkpoint = p.checkpoint ∧ s.encoded = p.encoded := by
 have n : p.logical.reads.n = 57607 := p.logical.n_eq.trans p.extent
 have length : p.proof.val.length = 58295 := by
  have h := p.logical.reads.proofLength
  rw [←p.proof_eq] at h
  simpa only [bytes,List.length_map,RSL.AFTERSTATE_BYTES,n] using h
 have ordered : 688#usize ≤ 58295#usize := by scalar_tac
 have bounded : (58295#usize).val ≤ p.proof.length := by change (58295#usize).val ≤ p.proof.val.length; rw [length]; scalar_tac
 obtain ⟨pr,range,equal⟩ := NNH_SliceRangeOk.value p.proof 688#usize 58295#usize ordered bounded
 have shape := (AdapterRw.Ranges.suffix_exact p.proof pr 688#usize 58295#usize
  ordered (by simpa using length) range).2
 change p.proof.val = p.proof.val.take 688 ++ pr.val at shape
 have suffix : bytesOf p.proof.val = (bytesOf p.proof.val).take 688 ++ bytesOf pr.val := by
  simpa only [bytesOf,List.map_append,List.map_take] using congrArg bytesOf shape
 exact ⟨⟨p.proofAccount,p.checkpointAccount,p.proof,p.checkpoint,p.encoded,pr,58295#usize⟩,
  ⟨p.proof_index,p.checkpoint_index,p.proof_read,p.checkpoint_read,range,length,suffix,
   ⟨p.validated,p.validate,p.encode⟩,equal⟩,rfl,rfl,rfl⟩

theorem join (ops : _root_.AdapterRw.Ops) (id : Program) (e1 e2 : S2W_D189Entry.Entry)
 (data : Slice U8) (clock : Slot) (saved : alloc.vec.Vec U8) (f : FirstCut) (s : SecondCut)
 (first : NNC_FirstCuts.Facts ops e1.first saved f)
 (second : Facts ops id (e2.second S2W_D189Wrappers.secondSizes) data clock s) :
 NNC_SourceCuts.Cuts ops e1.first (e2.second S2W_D189Wrappers.secondSizes) saved f s ∧
 P2P_Origin.Fact ops id (e2.second S2W_D189Wrappers.secondSizes) data clock s :=
 ⟨⟨first.proofIndex,first.publicIndex,first.proofRead,first.publicRead,first.decode,
 first.first,first.proofLength,first.suffix,second.proofIndex,second.checkpointIndex,
 second.proofRead,second.checkpointRead,second.range,second.length,second.suffix⟩,second.origin⟩
#print axioms produce
#print axioms join
end AspisR1.NNH_WeakReaderCuts
end
