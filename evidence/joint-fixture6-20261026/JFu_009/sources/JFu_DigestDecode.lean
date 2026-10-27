import S6N_Installation
import JFv_WordCanonical
import JFv_SelectedBytes
set_option autoImplicit false
namespace AspisR1.JFu_DigestDecode
open Aeneas Aeneas.Std Result WP
open AspisR1TerminalDecoder
open OraclePortCompactDraft MultiproofConeCanonical

@[local step] theorem word (arr : Array U8 4#usize) (canon : canonical (bytesOf arr.val)) :
    aspis_core.field.M31.from_le_bytes arr
      ⦃ out => out=some (core.num.U32.from_le_bytes arr) ⦄ := by
  have bound:=JFv_WordCanonical.bound arr canon
  unfold aspis_core.field.M31.from_le_bytes
  simp only [bind_tc_ok]
  have small : ¬(core.num.U32.from_le_bytes arr) ≥ aspis_core.field.P := by
    change ¬(core.num.U32.from_le_bytes arr).val ≥ 2147483647
    omega
  simp only [ge_iff_le,decide_eq_false small, Bool.false_eq_true,↓reduceIte,WP.spec_ok]

/-- Only eight scalar word decodes; no whole public decoder reduction. -/
theorem success (arr : Array U8 32#usize) (canon : canonical (bytesOf arr.val)) :
    ∃ out,atomic_statement.decode_digest_canonical arr=ok (.Ok out) := by
  have spec : atomic_statement.decode_digest_canonical arr ⦃ out => ∃ q,out=.Ok q ⦄ := by
    unfold atomic_statement.decode_digest_canonical
    step*
  obtain ⟨out,call,q,same⟩:=WP.spec_imp_exists spec
  exact ⟨q,by rw [same] at call;exact call⟩

#print axioms word
#print axioms success
end AspisR1.JFu_DigestDecode
