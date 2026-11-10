import NPH_R22FIqTerminal
import NNG_LIBTerminal

/-! NPH_ (R22, FIq step 3): site lemmas for the two model-layer wrappers of the terminal that the
backward referrer screen (NPH_fiq_refs_host.py, NPH_FIQ_REFS.json) leaves as TIE_CANDIDATE.
- `lib_native_ok`: LIB_VTerminal.native a is ok (never fail/div) whenever LIB_VTerminal.Domain a.
  The library carriers are canonical by type (LIB_VTerminalCarriers.claims_canonical/array_canonical/
  scalar_canonical); Domain gives the digest domain and the asset bound.
- `lib_model_site`: LIB_VTerminal.model, the only definition referrer of native, runs native only
  under Domain (otherwise it returns fail before native), and there native is ok.
- `nng_native_ok`: NNG_ModelTerminal.native at the lowered LIB arguments is LIB_VTerminal.native
  (closure theorem NNG_LIBTerminal.native), hence ok under Domain.
Standard axioms. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.NPH_R22FIqSites
open Aeneas Aeneas.Std Result
open LIB_VCarriers LIB_VTerminalCarriers

theorem lib_native_ok (a : LIB_VTerminal.Args) (h : LIB_VTerminal.Domain a) :
    ∃ out, LIB_VTerminal.native a = ok out := by
  unfold LIB_VTerminal.native
  exact NPH_R22FIqTerminal.qm31_ok _ _ _ _ h.1 (claims_canonical a.2.1) (array_canonical a.2.2.1)
    (array_canonical a.2.2.2.zc) (scalar_canonical a.2.2.2.lambda) (scalar_canonical a.2.2.2.chi)
    (scalar_canonical a.2.2.2.theta) (scalar_canonical a.2.2.2.mu) h.2
#print axioms lib_native_ok

theorem lib_model_site (a : LIB_VTerminal.Args) :
    (¬ LIB_VTerminal.Domain a ∧ LIB_VTerminal.model a = .fail .arrayOutOfBounds) ∨
    (LIB_VTerminal.Domain a ∧ ∃ out, LIB_VTerminal.native a = ok out) := by
  classical
  by_cases h : LIB_VTerminal.Domain a
  · exact Or.inr ⟨h, lib_native_ok a h⟩
  · exact Or.inl ⟨h, by simp only [LIB_VTerminal.model, dif_neg h]⟩
#print axioms lib_model_site

open NNG_Transport NNG_LIBScalar NNG_LIBArrays in
theorem nng_native_ok (a : LIB_VTerminal.Args) (h : LIB_VTerminal.Domain a) :
    ∃ out, NNG_ModelTerminal.native (fromT9 a.1) (lowerClaims a.2.1) (lowerArray a.2.2.1)
      (lowerChallenges a.2.2.2) = ok out := by
  rw [NNG_LIBTerminal.native a]
  exact lib_native_ok a h
#print axioms nng_native_ok

end AspisR1.NPH_R22FIqSites
