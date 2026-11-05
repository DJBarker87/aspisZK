import NGM_DotABI
set_option autoImplicit false
noncomputable section
namespace AspisR1.NGM_DotInduction
open Aeneas Aeneas.Std Result
abbrev Dot := FIo_Native.fast_pairing.EbyKDot
abbrev Item := NEV_DotCarrier.NE × NEV_DotCarrier.NQ
/-- Decoded-item iteration. This law does not assert a byte decoder or a
finish projection; those are separate outstanding associations. -/
def walk (logged : Bool) : List Item → Dot → Result (core.result.Result Dot Unit)
 | [],state => ok (.Ok state)
 | (value,scalar)::rest,state => do
   let (reply,updated) ← if logged then
     NFG_PublicG.run state scalar
       (FIo_Native.fast_pairing.canonical.Dot.push state.c0 (NFE_NFC_CalleeDomains.q value.c0) (NFE_NFC_CalleeDomains.q scalar))
       (FIo_Native.fast_pairing.canonical.Dot.push state.c1 (NFE_NFC_CalleeDomains.q value.c1) (NFE_NFC_CalleeDomains.q scalar))
     else FIo_Native.fast_pairing.EbyKDot.push state value scalar
   match reply with
   | .Err () => ok (.Err ())
   | .Ok () => walk logged rest updated

theorem native_model (items : List Item) (state : Dot) :
 walk true items state=walk false items state := by
 induction items generalizing state with
 | nil => rfl
 | cons item rest ih =>
   rcases item with ⟨value,scalar⟩
   simp only [walk, Bool.true_eq, if_true, Bool.false_eq, if_false,
     NFG_PublicG.source]
   congr 1
   funext reply
   rcases reply with ⟨reply,updated⟩
   cases reply with
   | Err unit => cases unit;rfl
   | Ok unit => cases unit;exact ih updated
#print axioms native_model
end AspisR1.NGM_DotInduction
end
