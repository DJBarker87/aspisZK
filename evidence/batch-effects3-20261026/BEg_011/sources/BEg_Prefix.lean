import BEg_Terminal
import BEf_Pure
import RPx_AttemptPrefix
set_option autoImplicit false
noncomputable section
namespace AspisR1.BEg_Prefix
open Aeneas Aeneas.Std Result SdkC_Source

/-- Canonicalizing a terminal rejection preserves RPx's attempted-address
occurrences exactly, including duplicates and the final failing call. -/
theorem addresses {A E : Type} (hashv : Parts → Result Digest)
    (code : Code (core.result.Result A E)) (before : Log) :
    RPx_AttemptPrefix.addresses
      (SdkC_Source.run hashv (BEg_Terminal.terminal code) before).2 =
    RPx_AttemptPrefix.addresses (SdkC_Source.run hashv code before).2 := by
  have effects := BEg_Terminal.effects (BEf_Pure.call (S := Unit) hashv) code () before
  rw [BEf_Pure.exact,BEf_Pure.exact] at effects
  exact congrArg (fun out : Unit × Log => RPx_AttemptPrefix.addresses out.2) effects

theorem attempted_count {A E : Type} (hashv : Parts → Result Digest)
    (code : Code (core.result.Result A E)) (before : Log) :
    (SdkC_Source.run hashv (BEg_Terminal.terminal code) before).2.length =
      (SdkC_Source.run hashv code before).2.length := by
  have effects := BEg_Terminal.effects (BEf_Pure.call (S := Unit) hashv) code () before
  rw [BEf_Pure.exact,BEf_Pure.exact] at effects
  exact congrArg (fun out : Unit × Log => out.2.length) effects

#print axioms addresses
#print axioms attempted_count
end AspisR1.BEg_Prefix
end
