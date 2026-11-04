import NGO_QAssociation
import FIq_S_RawActualDecodeKMainAdapter
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace NGO_ZeroLaw
open AspisR1DecodeKFullV10
/-- The emitted zero array has the exact native initializer at every index. -/
theorem initial (N : Usize) (i : Nat) (live : i<N.val) :
    (Array.repeat N aspis_core.field.QM31.ZERO).val[i]'(by
      rw [(Array.repeat N aspis_core.field.QM31.ZERO).property];exact live)=
        aspis_core.field.QM31.ZERO := by simp [Array.repeat]
/-- Literal carrier transport preserves the zero initializer for every N. -/
theorem port (N : Usize) :
    AspisR1PublicPreparation.RawActualDecodeKMainAdapter.decoderArrayToMain
      (Array.repeat N aspis_core.field.QM31.ZERO)=
        Array.repeat N AspisR1PublicPreparation.field.QM31.ZERO := by
  apply Subtype.ext
  simp [AspisR1PublicPreparation.RawActualDecodeKMainAdapter.decoderArrayToMain,
    AspisR1PublicPreparation.RawActualDecodeKMainAdapter.decoderQMToMain,Array.repeat]
#print axioms initial
#print axioms port
end NGO_ZeroLaw
