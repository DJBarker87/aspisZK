import NMT_345MapValidator
import NMT_R2_ValidatorObservation
set_option autoImplicit false
noncomputable section
namespace NMT_R2_345AtValidator
open Aeneas Aeneas.Std NMT_345 RSL

def install (c : Calls) : Calls := installMapErr {c with c7 := validateCall}

theorem boundary {W : Type} (c : Calls) (s : Decoded W) :
 raw07 (install c) s =
 match NMT_R2_ValidatorTotal.fresh s.statement with
 | .Ok _ => raw08 (install c) s
 | .Err _ => .ok (.Err .InvalidAccountData) := by
 rw [validator_call]
 change (do let r ← validateCall s.statement; mapValidator (install c) ⟨s,r⟩) = _
 rw [NMT_R2_ValidatorTotal.emitted]
 simp only [bind_tc_ok]
 exact validator_map_std {c with c7 := validateCall} ⟨s,NMT_R2_ValidatorTotal.fresh s.statement⟩

theorem observation {W : Type} (s : Decoded W) (env : Env) :
 RS.check (!NMT_R2_PublicLibrary.valid s.statement) .invalidAccountData env
  (NMT_R2_ValidatorObservation.run s.statement) := NMT_R2_ValidatorObservation.law s.statement env
#print axioms boundary
#print axioms observation
end NMT_R2_345AtValidator
end
