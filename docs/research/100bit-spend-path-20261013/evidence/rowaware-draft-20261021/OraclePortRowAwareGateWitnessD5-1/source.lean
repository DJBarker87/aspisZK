import OraclePortRowAwareRecognizedD4
import RawCutLiteralTranscriptSuccessor

set_option autoImplicit false
noncomputable section
namespace AspisR1.OraclePortRowAwareGateWitnessD5
open FS FS2 FS2.Duplex R0C.V3 AspisV8PairedCommitment
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisV8R19.AdaptiveFirstReadLaw
open CanonicalAddressEmbedding OracleDecisionMultiDecoder
open OraclePortRowAwareCausalD1 OraclePortRowAwareWitnessD2
open OraclePortRowAwareRecognizedD4

def prefix : List (Bytes × State) :=
  [(initial.toBytes,s0),(row0.toBytes,absorbed),(squeezed,answer),(advanced.toBytes,endpoint)]

def hash (a : Bytes) : State := (support a).getD (fun _ => 6)
def proof : LiteralProtocol.Proof := fun n => if n = 0 then .initial zero default else .payload m1

theorem support_cached : ∀ q ∈ prefix, support q.1 = some q.2 := by
  have hi := (support_fibers.1 initial.toBytes).mpr rfl
  have hr := (support_fibers.2.1 row0.toBytes).mpr rfl
  have ha := (support_fibers.2.2 advanced.toBytes).mpr rfl
  have hs : support squeezed = some answer := by
    have hl := byte_lengths
    have hlen : squeezed.length = 33 := by
      simp [squeezed,squeezeA,Addr.toBytes_ofBytes,squeeze,bytes_length]
    have h0 : squeezed ≠ initial.toBytes := by intro h; have := congrArg List.length h; omega
    have h1 : squeezed ≠ row0.toBytes := by intro h; have := congrArg List.length h; omega
    have h2 : squeezed ≠ advanced.toBytes := by
      simp only [squeezed,advanced,squeezeA,advanceA,Addr.toBytes_ofBytes,squeeze,advance]
      simp
    simp only [support,if_neg h0,if_neg h1,if_neg h2,ite_true]
  intro q hq
  simp only [prefix,List.mem_cons,List.mem_singleton] at hq
  rcases hq with rfl | rfl | rfl | rfl <;> assumption

theorem hash_cached : ∀ q ∈ prefix, hash q.1 = q.2 := by
  intro q hq
  simp only [hash,support_cached q hq,Option.getD_some]

theorem initial_eval (D : LiteralByteProtocol.Decoder) :
    eval hash ((LiteralByteProtocol.protocol D).chain hash pub proof 0).toProgram =
      (prefix, (TranscriptView.liftChallenge (p.σ 0 answer,endpoint))) := by
  have h0 : hash initial.toBytes = s0 := hash_cached _ (by simp [prefix])
  have h1 : hash row0.toBytes = absorbed := hash_cached _ (by simp [prefix])
  have hs : hash squeezed = answer := hash_cached _ (by simp [prefix])
  have ha : hash advanced.toBytes = endpoint := hash_cached _ (by simp [prefix])
  change eval hash (LiteralByteSampler.samp 0 ⟨pub,[]⟩ (.initial zero default)).toProgram = _
  rw [LiteralByteSampler.eval_eq]
  change mapView Addr.toBytes
    (eval (fun a => hash a.toBytes)
      (DuplexSamplers.initial p initial (PublicInitFrame.row0 p
        (by norm_num [p,SelectedTranscriptParams.params,SelectedTranscriptParams.D]))
        0 TranscriptView.liftChallenge).toProgram) = _
  rw [DuplexSamplers.initial_eval,h0]
  change mapView Addr.toBytes
    ([(initial,s0),(row0,hash row0.toBytes),
      (squeezeA p (hash row0.toBytes),hash (squeezeA p (hash row0.toBytes)).toBytes),
      (advanceA p (hash row0.toBytes),hash (advanceA p (hash row0.toBytes)).toBytes)],
      TranscriptView.liftChallenge (p.σ 0 (hash (squeezeA p (hash row0.toBytes)).toBytes),
        hash (advanceA p (hash row0.toBytes)).toBytes)) = _
  rw [h1,hs,ha]
  rfl

theorem firstCell_map {I J A C : Type} [DecidableEq I] [Inhabited A]
    (f : I → J) (s : Sampler I A C) :
    firstCell (ProgramSamplerMap.map f s) = (firstCell s).map f := by
  cases s <;> rfl

theorem first_node (D : LiteralByteProtocol.Decoder) :
    firstCell ((LiteralByteProtocol.protocol D).chain hash pub proof 1) = some node := by
  have hs := RawCutLiteralTranscriptSuccessor.actual_successor_state D hash pub proof 0
  rw [initial_eval D] at hs
  change UnifiedSampler.stateOf p (LiteralTranscript.erasePrefix
    ((LiteralByteProtocol.protocol D).transcript hash pub proof 1)) = endpoint at hs
  change firstCell (ProgramSamplerMap.map Addr.toBytes (LiteralTranscript.samp 1
    ((LiteralByteProtocol.protocol D).transcript hash pub proof 1) (.payload m1))) = _
  rw [firstCell_map]
  change (firstCell (UnifiedSampler.samp p
    (by norm_num [p,SelectedTranscriptParams.params,SelectedTranscriptParams.D]) 1
    (LiteralTranscript.erasePrefix ((LiteralByteProtocol.protocol D).transcript hash pub proof 1))
    (.payload m1))).map Addr.toBytes = _
  rw [UnifiedSampler.row_ordinary p _ 1 (by decide) (by decide) (by decide)]
  change some (absorbA p (UnifiedSampler.stateOf p (LiteralTranscript.erasePrefix
    ((LiteralByteProtocol.protocol D).transcript hash pub proof 1))) (p.lbl 1)
    (p.enc m1) (p.encLen m1)).toBytes = _
  rw [hs]
  apply congrArg some
  simp only [absorbA,Addr.toBytes_ofBytes,absorb]
  exact node_absorb.symm

theorem gate_node (D : LiteralByteProtocol.Decoder) : Gate D node support := by
  refine ⟨hash,pub,proof,1,by decide,?_,first_node D⟩
  refine ⟨⟨rfl,zero,default,rfl⟩,?_,initial.toBytes,emptyTable,rfl,?_,?_⟩
  · rw [initial_eval D]
    exact support_cached
  · intro a v h
    cases h
  · exact BinDecoderInitialStarts.recognizes_initial pub zero (by decide) rfl emptyTable

#print axioms support_cached
#print axioms hash_cached
#print axioms initial_eval
#print axioms firstCell_map
#print axioms first_node
#print axioms gate_node
end AspisR1.OraclePortRowAwareGateWitnessD5
end
