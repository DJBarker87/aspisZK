import NNH_Run5bPacket
import NNH_Run5bClock
import NNH_Run6Producers
import NNT_TopL
import NNT_G1aLaw
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNH_Run6NMF
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry S2W_D189Wrappers
open NNH_Run5bCtx NNH_Run5bHost NNH_Libraries S2W_NativeConsolidation
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw MultiproofConeCanonical NNH_Run5bPacket
variable {W Tx : Type} (L0 : Library W (Nat → Record))
 (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
 (std : S2W_TrustedStd.TrustedStd copy)

abbrev S := NNH_G1aEnv.sig (S_host (Tx := Tx) L0 copy std)
def recSig : RSL.EVB.RecSig (S (Tx := Tx) L0 copy std) where
 Realizes := (NNH_Run5bExec.recSig L0 copy std).Realizes
 EventRec := (NNH_Run5bExec.recSig L0 copy std).EventRec
 SelectsPair := (NNH_Run5bExec.recSig L0 copy std).SelectsPair

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
 obtain ⟨p⟩ := NNH_Run6Producers.produce L0 copy std c post o.events ref accepted game
 exact ⟨packet copy c p sel,p,sel,rfl⟩

theorem rootImage (c : Ctx W Tx) (q : NNH_NMFPrime.Packet (GExq_AccountExperiment.Outcome Bool) Unit Unit)
 (h : Associated copy c q) (root : NLP_InputDomain.Root0 q.s.checkpoint q.s.proof) :
 (S (Tx := Tx) L0 copy std).Root0Native c := by
 obtain ⟨p,sel,rfl⟩ := h
 exact NNR_RootImage.M3 L0 copy std c p.f p.s (cuts c p) root

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

#print axioms selected
#print axioms rootImage
#print axioms eventImage
#print axioms nmfB
end AspisR1.NNH_Run6NMF
end
