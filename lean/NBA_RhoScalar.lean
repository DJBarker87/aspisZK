import NBA_Rho
import NBA_Transcript
set_option autoImplicit false
namespace AspisR1.NBA_RhoScalar
open Aeneas Aeneas.Std Result AspisR1PublicPreparation

theorem source {H : Type} (D : aspis_core.Digest32 H)
    (before after : transcript.Transcript H) (row : U8) (payload : Slice U8)
    (block : Array U8 32#usize) (digits : List Nat) (last : List UInt32)
    (q : aspis_core.field.QM31)
    (call : transcript.Transcript.block D before row payload=ok (block,after))
    (trace : LPk_Induction.Digits 4 (SamplerBytePass.digits block) digits last)
    (packed : NBA_Rho.coordinates q=digits) :
    PreparedModel.scalar_k NBA_Installed.actual.sampling D before row payload=ok (q,after) := by
  have sample := NBA_Rho.source block digits last q trace packed
  have fromQm : NBA_Installed.actual.sampling.fromQm q=
      ok (PreparedFromQmSourceBridge.fromQmEmbedding q) :=
    PreparedFromQmSourceBridge.fromQmSource_success q
  unfold PreparedModel.scalar_k
  rw [call,bind_tc_ok]
  dsimp! only
  rw [sample,bind_tc_ok]
  simp only [lift,bind_tc_ok,fromQm]
  rfl

#print axioms source
end AspisR1.NBA_RhoScalar
