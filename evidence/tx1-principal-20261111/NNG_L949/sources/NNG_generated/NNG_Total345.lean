import RPz7_S6NativeForestDecodeTotalV1
import NMT_345Decoder
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_Total345
open Aeneas Aeneas.Std Result AspisR1TerminalDecoder
open pool_v1.pair_forest_terminal
/-- Reuse the symbolic native-model totality lemma; no decoder input buffer
is evaluated. The native certificate remains the existing CLOSED332 bridge. -/
theorem public_decoder (bytes : Slice U8) : ∃ r,NFY_NEX_PublicModel.run bytes=ok r := by
 obtain ⟨r,run⟩ := AspisS6NativeForestDecode.decode_total bytes
 have association := congrArg (fun x=>x.1) (NFY_NEX_TerminalOracle.result_state_effects bytes ())
 dsimp only at association
 have native := association.trans run
 unfold NFY_NEX_PublicModel.run
 rw [native,bind_tc_ok]
 cases r with
 | Ok st=>exact ⟨_,rfl⟩
 | Err e=>exact ⟨_,rfl⟩
#print axioms public_decoder

theorem decoder (bytes : Slice U8) : ∃ r,NMT_345.decodeCall bytes=ok r := by
 obtain ⟨r,run⟩ := public_decoder bytes
 rw [NMT_345.decode_closed,run]
 exact ⟨_,rfl⟩
#print axioms decoder
end AspisR1.NNG_Total345
