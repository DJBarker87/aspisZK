import ARS_Coverage
import ARS_AdaptiveCost
set_option autoImplicit false
noncomputable section
namespace AspisR1.ARS_PaddedSupport
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry S2W_D189Wrappers
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw SCE_Experiment S2W_D189Consolidation

/-- Conditional installed-domain cost obstruction. Preserve the original
extraction configuration, both native successes, runtime admissions, all four
bank-game fields and RuntimePersistence. The root's first-only query premise
also survives, but the account's original total work exceeds Q+1921. -/
theorem unbounded {W A C Tx : Type} (L : Library W (Nat → Record))
    (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
    (allocator : Allocator A) (c : DrvC_Installation.Configuration FIo_Install.W C)
    (err : C) (r : NP6_StdModel.Reservation)
    (native1 : S2W_ExtractionBoundary.First) (native2 : S2W_ExtractionBoundary.Second)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (extraction : S2W_DigestExtraction.AeneasExtraction
      (DrvC_Installation.sdk (FIp_Install.configuration err c r)) native1 native2 hashv)
    (a : Adversary A) (H : Bytes → State)
    (n : ARQ_WorldSupport.NativeAt (Tx := Tx) L copy allocator c err r native1 native2 hashv a H)
    (Q : Nat) (queries : ∀ K, (eval K (submission a)).1.length ≤ Q) :
    ∃ b : Adversary A,
      submission b = submission a ∧
      Nonempty (ARQ_WorldSupport.NativeAt (Tx := Tx) L copy allocator c err r native1 native2 hashv b H) ∧
      (∀ K, (eval K (submission b)).1.length ≤ Q) ∧
      ARS_AccountReplay.Consistent (account (FIp_Install.configuration err c r) hashv copy allocator CPH_Program.verifier b) H H ∧
      Q+1921 < (eval H (account (FIp_Install.configuration err c r) hashv copy allocator CPH_Program.verifier b)).1.length := by
  have replies := ARQ_NativeReplies.accepted c err r hashv copy allocator native1 native2 extraction
    n.sha256 H n.p1 n.syscall a CPH_Program.verifier n.saved n.post1 n.post2 n.final1 n.final2 n.accepted1 n.accepted2
  obtain ⟨b,submitted,_,consistent,cost,firstEq,secondEq⟩ := ARS_AdaptiveCost.unbounded
    (FIp_Install.configuration err c r) hashv copy allocator CPH_Program.verifier a [] H
    n.saved n.post1 n.final1 replies.1 (Q+1921) replies.2.2
  refine ⟨b,submitted,⟨⟨n.sha256,n.p1,n.syscall,n.saved,n.post1,n.post2,n.final1,n.final2,n.w1,n.w2,
    ?_,?_,?_,?_,n.p,n.t,n.u,n.actions,?_,n.RuntimePersistence⟩⟩,?_,consistent,cost⟩
  · simpa only [firstEq] using n.admission1
  · simpa only [secondEq] using n.admission2
  · simpa only [firstEq] using n.accepted1
  · simpa only [secondEq] using n.accepted2
  · rw [secondEq,firstEq]
    exact n.game
  · intro K
    rw [submitted]
    exact queries K

#print axioms unbounded
end AspisR1.ARS_PaddedSupport
end
