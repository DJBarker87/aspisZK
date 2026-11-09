import NNH8_Native
import NNH_Run6NMF
set_option autoImplicit false
noncomputable section
/-! Run 7 (G0 FINAL): NNH_Run5bPacket and NNH_Run6NMF restated at NOC_Run5bHost.S_host.
Only the host namespaces, the cut producers (NNH8_Producers) and the root image
(NNR_RootImage.at_entry at the corrected sdk, the body of NNR_RootImage.M3) change. -/
namespace AspisR1.NNH8_Packet
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry S2W_D189Wrappers
open NOC_Run5bCtx NOC_Run5bHost NNH_Libraries S2W_NativeConsolidation
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw
open MultiproofConeCanonical
variable {W Tx : Type}

abbrev Cut (c : Ctx W Tx) := NNH8_NativeCuts.Packet (NNR_Retime.atSlot c)

theorem cuts (c : Ctx W Tx) (p : Cut c) :
 NNC_SourceCuts.Cuts (sdk c) c.i.entry.first (c.j.entry.second secondSizes) c.world.saved p.f p.s := by
 have h := p.cuts
 rw [NNH8_Retime.sdk_same] at h
 exact h

def source
 (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
 (c : Ctx W Tx) := NNH_RecordedCharge.source copy (base c) c.fixed.indexError
 c.fixed.reservation (hashv c) c.fixed.a (c.fixed.Q0+c.fixed.Q1)

def select (c : Ctx W Tx) := ARQ_Observer.select (A := Bool) (configuration c) CPH_Program.verifier

def packet
 (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
 (c : Ctx W Tx) (p : Cut c)
 (sel : select c (eval c.sha256 (source copy c)).2 =
 P2P_NativeSelection.pair (sdk c) CPH_Program.verifier c.i.entry c.j.entry c.j.data c.j.slot) : NNH_NMFPrime.Packet (GExq_AccountExperiment.Outcome Bool) Unit Unit := by
 have native := NNR_Lift.M2 c.sha256 c.fixed.pda
  (NND_Carrier.reply NND_Carrier.slot c.j.slot) c.fixed.reservation
  p.s.pub p.s.proof p.s.checkpoint p.records p.events p.domain p.native
 let records := Classical.choose native
 let ev := Classical.choose (Classical.choose_spec native)
 have step := Classical.choose_spec (Classical.choose_spec native)
 exact (⟨source copy c,ARQ_Observer.project,select c,c.fixed.Q0+c.fixed.Q1,
  fun H => (VerifierCallBudget.firstReads_le_length _ _).trans (ARX_LocalCharge.budget _ _ H),
  c.sha256,sdk c,CPH_Program.verifier,c.i.entry,c.j.entry,c.j.data,c.j.slot,sel,
  c.world.saved,p.f,p.s,cuts c p,NNH8_Producers.origin c p,
  p.writerRoot,p.persisted,p.writerHeader,LIBB_PartitionEnv.digest (envOf c),(),
  NNH_064Install.frame,p.domain,
  NNR_Oracle.M2e c.sha256 c.fixed.pda _ c.fixed.reservation,records,ev,step⟩ :
  NNH_NMFPrime.Packet _ Unit Unit)

#print axioms AspisR1.NNH8_Packet.cuts
#print axioms AspisR1.NNH8_Packet.packet
end AspisR1.NNH8_Packet
namespace AspisR1.NNH8_NMF
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry S2W_D189Wrappers
open NOC_Run5bCtx NOC_Run5bHost NNH_Libraries S2W_NativeConsolidation
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw MultiproofConeCanonical NNH8_Packet
variable {W Tx : Type} (L0 : Library W (Nat → Record))
 (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
 (std : S2W_TrustedStd.TrustedStd copy)

abbrev S := NNH_G1aEnv.sig (S_host (Tx := Tx) L0 copy std)
def recSig : RSL.EVB.RecSig (S (Tx := Tx) L0 copy std) where
 Realizes := (NNH8_Exec.recSig L0 copy std).Realizes
 EventRec := (NNH8_Exec.recSig L0 copy std).EventRec
 SelectsPair := (NNH8_Exec.recSig L0 copy std).SelectsPair

def Associated (c : Ctx W Tx) (q : NNH_NMFPrime.Packet (GExq_AccountExperiment.Outcome Bool) Unit Unit) : Prop :=
 ∃ (p : Cut c) (sel : select c (eval c.sha256 (source copy c)).2 =
 P2P_NativeSelection.pair (sdk c) CPH_Program.verifier c.i.entry c.j.entry c.j.data c.j.slot),
 q = packet copy c p sel

theorem selected (I0 : RSL.TAS.Impl L V0 VL) :
 ∀ c : Ctx W Tx, (S (Tx := Tx) L0 copy std).Exhibited c →
 (∀ a s env, RSL.TX2_213.Ref L D (RSL.TAS.lib V0 (fun _ _ => True) (NNT_G1aLaw.field (S_host (Tx := Tx) L0 copy std) I0).w)
  (RSL.TX1_344.asStage1 VL P C) a s env (I0.entry a s env)) →
 (∃ s', (I0.entry ((S (Tx := Tx) L0 copy std).args2 c)
  ((S (Tx := Tx) L0 copy std).state2 c) ((S (Tx := Tx) L0 copy std).env2 c)).exit = .ret (.ok (),s')) →
 (S (Tx := Tx) L0 copy std).Accepted1 c ((S (Tx := Tx) L0 copy std).model1 c) →
 (S (Tx := Tx) L0 copy std).Game c ((S (Tx := Tx) L0 copy std).model1 c) ((S (Tx := Tx) L0 copy std).model2 c) →
 (S (Tx := Tx) L0 copy std).Extraction c ((S (Tx := Tx) L0 copy std).model1 c) ((S (Tx := Tx) L0 copy std).model2 c) →
 (S (Tx := Tx) L0 copy std).Queries c ((S (Tx := Tx) L0 copy std).model1 c) →
 (recSig (Tx := Tx) L0 copy std).SelectsPair c →
 ∃ q, Associated copy c q := by
 intro c _ weak ⟨post,returned⟩ accepted game _ _ sel
 let o := I0.entry ((S (Tx := Tx) L0 copy std).args2 c)
  ((S (Tx := Tx) L0 copy std).state2 c) ((S (Tx := Tx) L0 copy std).env2 c)
 change o.exit = .ret (.ok (),post) at returned
 have eta : o = ⟨.ret (.ok (),post),o.events⟩ := by
  exact congrArg (fun exit => RSL.Obs.mk exit o.events) returned
 have ref := weak ((S (Tx := Tx) L0 copy std).args2 c) ((S (Tx := Tx) L0 copy std).state2 c) ((S (Tx := Tx) L0 copy std).env2 c)
 change RSL.TX2_213.Ref _ _ _ _ _ _ _ o at ref
 rw [eta] at ref
 obtain ⟨p⟩ := NNH8_Producers.produce L0 copy std c post o.events ref accepted game
 exact ⟨packet copy c p sel,p,sel,rfl⟩

theorem rootImage (c : Ctx W Tx) (q : NNH_NMFPrime.Packet (GExq_AccountExperiment.Outcome Bool) Unit Unit)
 (h : Associated copy c q) (root : NLP_InputDomain.Root0 q.s.checkpoint q.s.proof) :
 (S (Tx := Tx) L0 copy std).Root0Native c := by
 obtain ⟨p,sel,rfl⟩ := h
 exact (NNR_RootImage.at_entry (sdk c) c.i.entry c.j.entry c.world.saved p.f p.s (cuts c p)).mpr root

theorem eventImage (c : Ctx W Tx) (q : NNH_NMFPrime.Packet (GExq_AccountExperiment.Outcome Bool) Unit Unit)
 (h : Associated copy c q) : NNH_NMFPrime.charged q ↔ (recSig (Tx := Tx) L0 copy std).EventRec c := by
 obtain ⟨p,sel,rfl⟩ := h
 exact Iff.rfl

def nmfB (I0 : RSL.TAS.Impl L V0 VL) :
 NNT_TopL.NNC_NMFPrimeB (S (Tx := Tx) L0 copy std) L D V0 VL P C I0
 (NNT_G1aLaw.field (S_host (Tx := Tx) L0 copy std) I0) (recSig (Tx := Tx) L0 copy std) where
 root0_or_rec := by
  intro c hx entry accepted ac1 game ext queries sel
  obtain ⟨q,associated⟩ := selected L0 copy std I0 c hx entry accepted ac1 game ext queries sel
  rcases NNH_NMFPrime.alternative q with root | event
  · exact Or.inl (rootImage L0 copy std c q associated root.1)
  · exact Or.inr ((eventImage L0 copy std c q associated).mp event)

#print axioms AspisR1.NNH8_NMF.selected
#print axioms AspisR1.NNH8_NMF.rootImage
#print axioms AspisR1.NNH8_NMF.eventImage
#print axioms AspisR1.NNH8_NMF.nmfB
end AspisR1.NNH8_NMF
end
