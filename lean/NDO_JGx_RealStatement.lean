import NDO_JFs_PublicDecode
import NDO_JGx_PublicArray
import RPz7_S6CurrentCodecInstallationV1
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGx_RealStatement
open Aeneas Aeneas.Std Result

def value : AspisS6CurrentCodecInstallation.Statement :=
  AspisS6CurrentAdapterCarrier.fromPoolV1PairForestTerminalStatementV1 JFs_PublicValue.value

theorem native : AspisS6OuterNativeInstalled.encode JFs_PublicValue.value=ok (.Ok JGx_PublicArray.value) := by
  obtain ⟨encoded,run,bytes⟩ := AspisS6OuterNativeCodec.accepted_inverse JFx_NativeBytes.publicInput
    JFs_PublicValue.value JFs_PublicDecode.source
  have same : encoded=JGx_PublicArray.value := Subtype.ext bytes
  exact same ▸ run
#print axioms native

theorem encode : AspisS6CurrentCodecInstallation.encode value=ok (.Ok JGx_PublicArray.value) := by
  unfold AspisS6CurrentCodecInstallation.encode value
  rw [AspisS6CurrentAdapterCarrier.to_fromPoolV1PairForestTerminalStatementV1,native]
  rfl
#print axioms encode

theorem decode : AspisS6CurrentCodecInstallation.decode JFx_NativeBytes.publicInput=ok (.Ok value) := by
  unfold AspisS6CurrentCodecInstallation.decode
  rw [AspisS6CurrentCodecInstallation.boxed_eq]
  simp only [AspisS6CurrentCodecInstallation.boxOps,AspisS6CurrentCodecInstallation.rawDecoder,
    JFs_PublicDecode.source,AspisS6OuterNativeOps.resultMap,AspisS6CurrentCodecInstallation.mapBoth,bind_tc_ok]
  rfl
#print axioms decode
end AspisR1.JGx_RealStatement
end
