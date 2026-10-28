import R1Z.PV_RDCD_ContextTotal
import R1Z.ProverRwFullExternalFuns
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RDCD_ContextInstall
open Aeneas Aeneas.Std Result ProverRwFull
attribute [local instance] Classical.propDecidable
abbrev Native := ProverRwFull.aspis_core.state_only_hiding.StateOnlyHidingContext
abbrev Extracted := PV_RDCD_ContextTotal.Context

def encode (a : Native) : Extracted :=
  ⟨a.statement_digest,a.mask_nonce,a.mask_layout_fingerprint,a.layout_factor_fingerprint⟩
def decode (a : Extracted) : Native :=
  ⟨a.statement_digest,a.mask_nonce,a.mask_layout_fingerprint,a.layout_factor_fingerprint⟩
theorem roundtrip (a : Native) : decode (encode a) = a := by cases a; rfl
theorem inverse_roundtrip (a : Extracted) : encode (decode a) = a := by cases a; rfl

def nativeEq (a b : Native) : Result Bool := PV_RDCD_V216.context_eq (encode a) (encode b)
theorem native_total (a b : Native) : nativeEq a b = ok (decide (a=b)) := by
  rw [nativeEq, PV_RDCD_ContextTotal.total]
  have h : encode a = encode b ↔ a=b := ⟨fun h => by simpa only [roundtrip] using congrArg decode h, congrArg encode⟩
  simp only [h]

variable [ExternalTypes]
def selected (ops : ExternalFuns) : ExternalFuns := {ops with op114 := nativeEq}
theorem op114_complete (ops : ExternalFuns) (a b : Native) :
    (selected ops).op114 a b = ok (decide (a=b)) := native_total a b
/-- Direct law replacement at the original complete Result boundary. -/
theorem replace_law (old : Native → Native → Result Bool)
    (law : ∀ a b, old a b = ok (decide (a=b))) : nativeEq = old := by
  funext a b
  exact (native_total a b).trans (law a b).symm
#print axioms roundtrip
#print axioms inverse_roundtrip
#print axioms native_total
#print axioms op114_complete
#print axioms replace_law
end R1Z.PV_RDCD_ContextInstall
