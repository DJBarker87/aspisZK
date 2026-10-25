import Tx1Q_SameCut
import RawTx1DigestLog
import SdkC_Source
set_option autoImplicit false
noncomputable section
open Aeneas Aeneas.Std Result
namespace AspisR1.PAln_Oracle
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.SqueezeOracleBridge
open AspisR1PublicPreparation Tx1DigestLog

/-- Reached calls of the very installed TX1 digest have the same ROM value.
No syscall totality, invented successful call or all-address query is used. -/
theorem installed_backend {CoreError : Type} (adapterOps : AdapterRw.Ops)
    (ops : AspisR1CurrentCaller.Ops) (reserved : Bool)
    (query : Port3_NativeQueryBody.Ops) (geo : Port3_NativeGeometryBody.Ops CoreError)
    (B : FinishModel.Boundaries) (std : ClaimsUnrolledFinish.StdCalls)
    (native1 : S2W_ExtractionBoundary.First) (native2 : S2W_ExtractionBoundary.Second)
    (hashv : S2Z.Oracle.Parts → Result S2Z.Oracle.Digest)
    (extraction : S2W_DigestExtraction.AeneasExtraction
      (ClaimsUnrolledSdk.sdkOps adapterOps (Tx1Q_SameCut.dictionary ops reserved query geo) B std)
      native1 native2 hashv)
    (sha256 H : Bytes → State) (p1 : S2W_ExtractionBoundary.P1 sha256 H)
    (syscall : S2W_ExtractionBoundary.RuntimeSyscall hashv sha256) :
    ByteOracleBackend (AspisR1CurrentCaller.InstalledPreparation.retainedDigest
      (Tx1Q_SameCut.callerDigest adapterOps ops reserved query geo B std)) H := by
  intro q actual
  obtain ⟨hash,input,output,same,returned⟩ := actual
  cases hash
  subst q
  change (ClaimsUnrolledSdk.sdkOps adapterOps
    (Tx1Q_SameCut.dictionary ops reserved query geo) B std).op43 () input=ok output at returned
  rw [extraction.digestSource,S2W_DigestExtraction.digest_eq_hashv] at returned
  exact (syscall.returningValue input output returned).trans (p1.realization _)

theorem digest_dictionary {CoreError : Type} (adapterOps : AdapterRw.Ops)
    (ops : AspisR1CurrentCaller.Ops) (reserved : Bool)
    (query : Port3_NativeQueryBody.Ops) (geo : Port3_NativeGeometryBody.Ops CoreError)
    (B : FinishModel.Boundaries) (std : ClaimsUnrolledFinish.StdCalls)
    (native1 : S2W_ExtractionBoundary.First) (native2 : S2W_ExtractionBoundary.Second)
    (hashv : S2Z.Oracle.Parts → Result S2Z.Oracle.Digest)
    (extraction : S2W_DigestExtraction.AeneasExtraction
      (ClaimsUnrolledSdk.sdkOps adapterOps (Tx1Q_SameCut.dictionary ops reserved query geo) B std)
      native1 native2 hashv)
    : ∀ (self : Unit) (parts : S2Z.Oracle.Parts),
      (AspisR1CurrentCaller.InstalledPreparation.retainedDigest
        (Tx1Q_SameCut.callerDigest adapterOps ops reserved query geo B std)).digest self parts=hashv parts := by
  intro self parts
  cases self
  change (ClaimsUnrolledSdk.sdkOps adapterOps
    (Tx1Q_SameCut.dictionary ops reserved query geo) B std).op43 () parts=hashv parts
  rw [extraction.digestSource,S2W_DigestExtraction.digest_eq_hashv]

#print axioms digest_dictionary
#print axioms installed_backend
end AspisR1.PAln_Oracle
end
