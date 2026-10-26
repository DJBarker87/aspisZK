import F3T_Recovered
import F3T_Runtime
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3T_InstalledRecovered
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw
open F3T_Experiment F3T_Charged F3T_TwoPass F3T_ByteCarrier F3T_CanonicalJoin

theorem inputs {F C : Type} (c : DrvC_Installation.Configuration F C)
    (D : LiteralByteProtocol.Decoder) (P : ByteProver)
    (hashv : SdkC_Source.Parts → Aeneas.Std.Result SdkC_Source.Digest)
    (raw : AcceptedVerifierJoin c D (F3T_Installed.source c hashv))
    (H : Bytes → State)
    (accepted : (eval H (annotatedWith D (F3T_Installed.source c hashv)
      (F3T_Canon.canon (lift c P)))).2.2=true) :
    OraclePortRefineJoin.RecoveredInputAgreement
      (view (eval H (annotatedWith D (F3T_Installed.source c hashv) (F3T_Canon.canon (lift c P)))))
      (view (eval H (recorded D (build D) (F3T_Canon.canon (lift c P))))) :=
  F3T_ByteTransport.recovered c D _ (F3T_Installed.physical c hashv) raw P H accepted

#print axioms inputs
end AspisR1.F3T_InstalledRecovered
end
