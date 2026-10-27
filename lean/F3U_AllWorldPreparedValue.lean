import F3U_AllWorldPrepare
import F3U_RehashValue
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3U_AllWorldPreparedValue
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
      AspisR1PublicPreparation.PreparedHashCode.erase (F3U_Rehash.code H
        (SdkD_PrepareSource.code
          (Op5T_Concrete.current {(GExp_FirstPair.base c.currentBase c.reserved c.query c.geometry) with op16:=Tx1Q_Install.writer})
          c.boundaries c.std (currentDigest c) (AspisS6CurrentVerifierCarrier.toPublic semantic) proof ()
          (Array.repeat 29#usize zero)))=ok (.Ok p,scratch) := by
  obtain ⟨zero,p,scratch,prepare⟩ := F3U_AllWorldPrepare.accepted c hashv semantic pub proof H accepted
  refine ⟨zero,p,scratch,?_⟩
  rw [←F3U_RehashValue.value,←SdkD_PrepareLower.program,F3U_ReifyValue.value]
  exact prepare

#print axioms accepted
end AspisR1.F3U_AllWorldPreparedValue
end
