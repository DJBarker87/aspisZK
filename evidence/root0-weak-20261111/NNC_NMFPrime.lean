import NNC_BindingRoot
import TAS_Interfaces
set_option autoImplicit false
noncomputable section
namespace NNC_NMFPrime
open Aeneas Aeneas.Std AspisR1 MultiproofConeCanonical S2W_NativeConsolidation
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw FS FS2
open RSL.TAS
/-- Complete SAME-occurrence native inputs to the already proved NMF' core.
No second model Result/Calls, TX2 extraction.stage2 acceptance or reader Root0
is present. Producing this packet from weak entry facts remains an obligation. -/
structure Packet (A Ambient X : Type) where
 source : Program Bytes State A
 project : A → OraclePortCompactDraft.Parsed × (Fin 22 → Fin 262144)
 Q : Nat
 budget : ∀ H,firstReads emptyTable (eval H source).1≤Q+1921
 H : Bytes → State
 ops : AdapterRw.Ops
 id : S2W_ExtractionBoundary.Program
 e1 : S2W_D189Entry.Entry
 e2 : S2W_D189Entry.Entry
 data2 : Slice U8
 slot : S2W_ExtractionBoundary.Slot
 saved : alloc.vec.Vec U8
 f : FirstCut
 s : SecondCut
 cuts : NNC_SourceCuts.Cuts ops e1.first (e2.second S2W_D189Wrappers.secondSizes) saved f s
 origin : P2P_Origin.Fact ops id (e2.second S2W_D189Wrappers.secondSizes) data2 slot s
 writerRoot : NLP_InputDomain.Root0 saved.deref f.proof
 persisted : bytesOf s.checkpoint.val=bytesOf saved.val
 writerHeader : NLW_ReaderHeader.decode (bytesOf saved.val)=
  some (H (bytesOf f.proof.val),H (bytesOf f.pub.val))
 d : VTop_Stages.aspis_core.digest.Digest32 X
 hash : X
 world : NLM_PacketTypes.World Ambient
 domain : NNC_064Weak.Domain (NLW_Full064.Args.mk d s.pub s.proof s.checkpoint hash)
 oracle : CheckpointBytes5Inputs.Oracle (VTop_Checkpoint.digest d) hash H
 records : List (NLT_NativeInvocation.Occurrence H d hash)
 events : List (NLW_Full064.Event Ambient X)
 native : NMN_064.Native H ⟨⟨d,s.pub,s.proof,s.checkpoint,hash⟩,world⟩
  (.common (.resolved (Aeneas.Std.Result.ok (.Ok ())) records)) events

def charged {A Ambient X : Type} (p : Packet A Ambient X) : Prop :=
 BinRawByteCollisionTargets.event SelectedTranscriptParams.params.iv (p.Q+2965)
  (eval p.H (Hiq_RecordedJoint.program p.source p.project
   (fun _=>P2P_NativeSelection.pair p.ops p.id p.e1 p.e2 p.data2 p.slot)))

/-- Direct native alternative. The canonical common row is constructed only
in the Root0 branch; the collision branch carries no TX2 row conclusion. -/
theorem alternative {A Ambient X : Type} (p : Packet A Ambient X) :
 (NLP_InputDomain.Root0 p.s.checkpoint p.s.proof ∧
  NLT_CompleteRoot.RowSpec p.H p.d p.s.pub p.s.proof p.s.checkpoint p.hash) ∨ charged p :=
 NNC_BindingRoot.root0_or_existing_collision p.source p.project p.Q p.budget p.H
  p.ops p.id p.e1 p.e2 p.data2 p.slot p.saved p.f p.s p.cuts p.origin
  p.writerRoot p.persisted p.writerHeader p.d p.hash p.world p.domain p.oracle
  p.records p.events p.native

/-- Exact TAS field shape. This is an intermediate fold, NOT a candidate:
`selected` still has to be derived from the complete sibling row packets and
physical representation. It is not an allowed own-input clause of any row. -/
def assemble {A Ambient X : Type}
 (S : Sig) (L : RSL.PoolLib) (D : RSL.DeployedIds) (V0 : RSL.TX2_241.V2Lib)
 (VL : RSL.VLib) (P : RSL.PreparedNew VL) (C : RSL.TX1_345.S1Lib VL)
 (I : Impl L V0 VL) (g : RSL.TAS.NNC_G1a S L V0 VL I)
 (Associated : S.Ctx → Packet A Ambient X → Prop)
 (selected : ∀ c, S.Exhibited c →
  (∀ a s env, RSL.TX2_213.Ref L D (lib V0 (fun _ _=>True) g.w)
   (RSL.TX1_344.asStage1 VL P C) a s env (I.entry a s env)) →
  (∃ s', (I.entry (S.args2 c) (S.state2 c) (S.env2 c)).exit=.ret (.ok (),s')) →
  S.Accepted1 c (S.model1 c) → S.Game c (S.model1 c) (S.model2 c) →
  S.Extraction c (S.model1 c) (S.model2 c) → S.Queries c (S.model1 c) →
  ∃ p : Packet A Ambient X, Associated c p)
 (rootImage : ∀ c (p : Packet A Ambient X), Associated c p → NLP_InputDomain.Root0 p.s.checkpoint p.s.proof →
  S.Root0Native c)
 (eventImage : ∀ c (p : Packet A Ambient X), Associated c p → (charged p ↔ S.Event c (S.model1 c))) :
 RSL.TAS.NNC_NMFPrime S L D V0 VL P C I g where
 Ev := fun c=>S.Event c (S.model1 c)
 root0_or_event := by
  intro c exhibited entry accepted a1 game extraction queries
  obtain ⟨p,associated⟩ := selected c exhibited entry accepted a1 game extraction queries
  rcases alternative p with root | event
  · exact Or.inl (rootImage c p associated root.1)
  · exact Or.inr ((eventImage c p associated).mp event)

#print axioms alternative
#print axioms assemble
end NNC_NMFPrime
