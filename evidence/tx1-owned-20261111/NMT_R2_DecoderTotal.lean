import NMT_345Decoder
set_option autoImplicit false
noncomputable section
namespace NMT_R2_DecoderTotal
open Aeneas Aeneas.Std NMT_345

def reply : Option Statement → core.result.Result Statement PE
 | some s => .Ok s
 | none => .Err .InvalidAccountData

/-- Full CLOSED332 value law, ALL byte slices. The existing total forest
parser law is reused, including every rejected input, without expansion. -/
theorem result (bytes : Slice U8) : ∃ r, decodeCall bytes = .ok (reply r) := by
 obtain ⟨r,hr⟩ := AspisS6NativeForestDecode.decode_total bytes
 have source := congrArg (fun x => x.1)
  (NFY_NEX_TerminalOracle.result_state_effects bytes ())
 dsimp only at source
 rw [decode_closed]
 unfold NFY_NEX_PublicModel.run
 rw [source,hr]
 cases r with
 | Ok st => exact ⟨some _,rfl⟩
 | Err e => exact ⟨none,rfl⟩
#print axioms result
end NMT_R2_DecoderTotal
end
