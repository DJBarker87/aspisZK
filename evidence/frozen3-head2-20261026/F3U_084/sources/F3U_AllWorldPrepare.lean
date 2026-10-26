import F3U_ReifyFirst
import F3U_FirstCode
import F3S_FirstHeader
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3U_AllWorldPrepare
open Aeneas Aeneas.Std Result
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw
open DrvC_Installation

theorem accepted {F C : Type} (c : Configuration F C)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (semantic : Port1_Driver.Semantic) (pub proof : Slice U8) (H : Bytes → State)
    (accepted : (eval H (DrvC_PairProgram.source c hashv semantic pub proof)).2=true) :
    ∃ (zero : AspisR1CurrentCaller.aspis_core.field.wide_exact.WideExact)
      (p : AspisR1CurrentCaller.verifier.Prepared)
      (scratch : Array AspisR1CurrentCaller.aspis_core.field.wide_exact.WideExact 29#usize),
      CheckpointBytes5Effect.erase (SdkC_Source.dictionary (F3U_Oracle.hashv H)) ()
        (SdkD_PrepareLower.lower (SdkD_PrepareSource.code
          (Op5T_Concrete.current {(GExp_FirstPair.base c.currentBase c.reserved c.query c.geometry) with op16:=Tx1Q_Install.writer})
          c.boundaries c.std (currentDigest c) (AspisS6CurrentVerifierCarrier.toPublic semantic) proof ()
          (Array.repeat 29#usize zero)))=ok (.Ok p,scratch) := by
  obtain ⟨saved,first,second⟩ := F3U_ReifyFirst.first c hashv semantic pub proof H accepted
  rw [←F3U_FirstCode.same] at first
  have firstIdeal : CheckpointBytes5Effect.erase (SdkC_Source.dictionary (F3U_Oracle.hashv H)) ()
      (GExq_FirstCode.code (GExp_FirstPair.base c.currentBase c.reserved c.query c.geometry)
        c.boundaries c.std (F3U_Oracle.hashv H) (currentDigest c)
        (AspisS6CurrentVerifierCarrier.toPublic semantic) pub proof 10#usize ())=ok (.Ok saved) := first
  obtain ⟨zero,p,scratch,hzero,prepare,tail,logs⟩ := F3S_FirstHeader.split
    (GExp_FirstPair.base c.currentBase c.reserved c.query c.geometry) c.boundaries c.std
    (F3U_Oracle.hashv H) (currentDigest c) (AspisS6CurrentVerifierCarrier.toPublic semantic) pub proof 10#usize () saved firstIdeal
  exact ⟨zero,p,scratch,prepare⟩

#print axioms accepted
end AspisR1.F3U_AllWorldPrepare
end
