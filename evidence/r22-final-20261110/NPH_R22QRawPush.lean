import NFE_NFC_CalleeDomains
import NEV_DotInputs

/-! NPH_ (R22, Q.raw item): the FIo copy of canonical.Q.raw executes only inside
FIo_Native.fast_pairing.canonical.Dot.push, whose deployed caller is EbyKDot.push
(backward screen NPH_QRAW_REFS.json; other referrers are proof models).
- `checked_none`: checked_q returns Err (no Dot.push) on a scalar with a limb >= P.
- `push_total`: EbyKDot.push self v x is ok for EVERY state and scalar whenever the pushed value v
  is canonical: at the term limit it returns Err before any push; on a non-canonical scalar
  checked_q rejects before any push; otherwise NFE_NFC_CalleeDomains.total (both Dot.push calls,
  hence both Q.raw calls, on canonical limbs). So every Q.raw call executed by such a push is ok.
- `g_push_site`: in FIp_NativeDots.fast_dots.four_dots_one the pushed values are reads of g
  (g[28], g[26], g[27]); on NEV_DotInputs.Canonical g every such push is ok.
The remaining contexts (canonical g at every executed op20 dots call; the values pushed by the
FIo weights loops; the claim-dot pushes of the AspisR1CanonicalQRawUnified copy) are recorded in
NPH_R22_STATUS.md section 19e. Standard axioms. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.NPH_R22QRawPush
open Aeneas Aeneas.Std Result NEV_DotCarrier

theorem checked_none (x : NQ)
    (h : ¬ (x.c0.a<2147483647#u32 ∧ x.c0.b<2147483647#u32 ∧ x.c1.a<2147483647#u32 ∧ x.c1.b<2147483647#u32)) :
    FIo_Native.fast_pairing.checked_q x = ok (.Err ()) := by
  have check := NFE_NFC_CalleeDomains.from_limbs x.c0.a x.c0.b x.c1.a x.c1.b
  rw [if_neg h] at check
  simp only [FIo_Native.fast_pairing.checked_q, FIo_Native.fast_pairing.limbs_of, check, bind_tc_ok]
#print axioms checked_none

theorem push_total (self : FIo_Native.fast_pairing.EbyKDot) (v : NE) (x : NQ) (hv : canonE v) :
    ∃ r, FIo_Native.fast_pairing.EbyKDot.push self v x = ok r := by
  by_cases hc : self.count ≥ FIo_Native.fast_pairing.MAX_TERMS
  · refine ⟨(.Err (), self), ?_⟩
    simp only [FIo_Native.fast_pairing.EbyKDot.push, if_pos hc]
  · by_cases valid : x.c0.a<2147483647#u32 ∧ x.c0.b<2147483647#u32 ∧
        x.c1.a<2147483647#u32 ∧ x.c1.b<2147483647#u32
    · have hx : canonQ x := ⟨⟨by scalar_tac, by scalar_tac⟩, ⟨by scalar_tac, by scalar_tac⟩⟩
      have count : self.count.val < 4096 := by
        simp only [FIo_Native.fast_pairing.MAX_TERMS] at hc; scalar_tac
      obtain ⟨out, h, _⟩ := NFE_NFC_CalleeDomains.total self v x hv hx count
      exact ⟨_, h⟩
    · have i0 : Array.index_usize (Array.make 2#usize [NFE_NFC_CalleeDomains.q v.c0, NFE_NFC_CalleeDomains.q v.c1])
          0#usize = ok (NFE_NFC_CalleeDomains.q v.c0) := rfl
      have i1 : Array.index_usize (Array.make 2#usize [NFE_NFC_CalleeDomains.q v.c0, NFE_NFC_CalleeDomains.q v.c1])
          1#usize = ok (NFE_NFC_CalleeDomains.q v.c1) := rfl
      refine ⟨(.Err (), self), ?_⟩
      (simp only [FIo_Native.fast_pairing.EbyKDot.push, if_neg hc, NFE_NFC_CalleeDomains.from_wide,
        bind_tc_ok, checked_none x valid, core.result.Result.Insts.CoreOpsTry.branch, i0, i1]) <;> rfl
#print axioms push_total

theorem g_push_site (g : NEV_DotInputs.Coefficients) (hg : NEV_DotInputs.Canonical g) (i : Usize)
    (hi : i.val < 29) (we : NE) (hr : Array.index_usize g i = ok we)
    (self : FIo_Native.fast_pairing.EbyKDot) (x : NQ) :
    ∃ r, FIo_Native.fast_pairing.EbyKDot.push self we x = ok r :=
  push_total self we x (NEV_DotInputs.selected g hg i hi we hr)
#print axioms g_push_site

end AspisR1.NPH_R22QRawPush
