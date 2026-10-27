import F3V_OracleDictionary
import RawTx1DigestLog
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3V_IdealBackend
open Aeneas Aeneas.Std Result
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep AspisV8R19.SqueezeOracleBridge

theorem backend {Hash : Type} (H : Bytes → State)
    (D : AspisR1CurrentCaller.aspis_core.digest.Digest32 Hash) :
    AspisR1PublicPreparation.Tx1DigestLog.ByteOracleBackend
      (AspisR1CurrentCaller.InstalledPreparation.retainedDigest (F3V_OracleDictionary.current H D)) H := by
  intro q actual
  obtain ⟨hash,input,output,same,returned⟩ := actual
  subst q
  change F3U_Oracle.hashv H input=ok output at returned
  have eq : encodeState (H (flatten input))=output := Result.ok.inj returned
  rw [←eq]
  exact state_roundtrip _

#print axioms backend
end AspisR1.F3V_IdealBackend
end
