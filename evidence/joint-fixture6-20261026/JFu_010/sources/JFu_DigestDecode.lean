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
  apply exists_imp_spec
  refine ⟨some (core.num.U32.from_le_bytes arr),?_,rfl⟩
  unfold aspis_core.field.M31.from_le_bytes
  simp only [lift,bind_tc_ok]
  have small : ¬(core.num.U32.from_le_bytes arr) ≥ aspis_core.field.P := by
    change ¬(core.num.U32.from_le_bytes arr).val ≥ 2147483647
    omega
  simp only [ge_iff_le,decide_eq_false small, Bool.false_eq_true,↓reduceIte]

@[local step] theorem option {T E : Type} (o : Option T) (e : E) :
    core.option.Option.ok_or o e
      ⦃ out => out=(match o with | some v => .Ok v | none => .Err e) ⦄ := by
  cases o <;> simp only [core.option.Option.ok_or,WP.spec_ok]

theorem chunk (arr : Array U8 32#usize) (canon : canonical (bytesOf arr.val))
    (k : Nat) (hk : k<8) :
    canonical (bytesOf [arr.val[4*k]'(by rw [arr.property];omega),
      arr.val[4*k+1]'(by rw [arr.property];omega),
      arr.val[4*k+2]'(by rw [arr.property];omega),
      arr.val[4*k+3]'(by rw [arr.property];omega)]) := by
  let out : Slice U8 := ⟨[arr.val[4*k]'(by rw [arr.property];omega),
      arr.val[4*k+1]'(by rw [arr.property];omega),
      arr.val[4*k+2]'(by rw [arr.property];omega),
      arr.val[4*k+3]'(by rw [arr.property];omega)],by simp;scalar_tac⟩
  apply JFv_SelectedBytes.canonical_slice (Array.to_slice arr) out (4*k) 4 rfl
    (by simp only [Array.to_slice,Slice.length,arr.property];omega) (by omega) (by decide) canon
  intro j hj
  interval_cases j <;> simp only [out,Array.to_slice,List.getElem_cons_succ,List.getElem_cons_zero,Nat.add_zero]

/-- Only eight scalar word decodes; no whole public decoder reduction. -/
theorem success (arr : Array U8 32#usize) (canon : canonical (bytesOf arr.val)) :
    ∃ out,atomic_statement.decode_digest_canonical arr=ok (.Ok out) := by
  have spec : atomic_statement.decode_digest_canonical arr ⦃ out => ∃ q,out=.Ok q ⦄ := by
    unfold atomic_statement.decode_digest_canonical
    step*
    case canon =>
      simpa only [Array.make,i_post,i1_post,i2_post,i3_post] using chunk arr canon 0 (by decide)
    case canon =>
      simpa only [Array.make,i4_post,i5_post,i6_post,i7_post] using chunk arr canon 1 (by decide)
    case canon =>
      simpa only [Array.make,i8_post,i9_post,i10_post,i11_post] using chunk arr canon 2 (by decide)
    case canon =>
      simpa only [Array.make,i12_post,i13_post,i14_post,i15_post] using chunk arr canon 3 (by decide)
    case canon =>
      simpa only [Array.make,i16_post,i17_post,i18_post,i19_post] using chunk arr canon 4 (by decide)
    case canon =>
      simpa only [Array.make,i20_post,i21_post,i22_post,i23_post] using chunk arr canon 5 (by decide)
    case canon =>
      simpa only [Array.make,i24_post,i25_post,i26_post,i27_post] using chunk arr canon 6 (by decide)
    case canon =>
      simpa only [Array.make,i28_post,i29_post,i30_post,i31_post] using chunk arr canon 7 (by decide)
    all_goals simp_all only [o_post,o1_post,o2_post,o3_post,o4_post,o5_post,o6_post,o7_post,
      core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok]
    all_goals exact ⟨_,rfl⟩
  obtain ⟨out,call,q,same⟩:=WP.spec_imp_exists spec
  exact ⟨q,by rw [same] at call;exact call⟩

#print axioms word
#print axioms option
#print axioms chunk
#print axioms success
end AspisR1.JFu_DigestDecode
