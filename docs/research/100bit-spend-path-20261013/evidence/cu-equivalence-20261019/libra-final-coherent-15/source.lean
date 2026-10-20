import CuSavingsLibraReference
import CuSavingsLibraLoop
set_option autoImplicit false
namespace AspisR1.CuSavingsLibraReferenceLiteral
open Aeneas Aeneas.Std Result AspisR1Libra
open CuSavingsLibraSourceModel CuSavingsLibraSourceControl
open CuSavingsLibraReferencePowers (Extra)
open CuSavingsLibraReferenceLoop (Low block partialSum term)
variable {R S : Type} [CommSemiring R] [CommSemiring S] [Shared]
variable (A : Arithmetic R S)

def challenge (extra : Extra) (side : Nat) : R :=
  A.embedding (A.decodeK (lookup extra field.QM31.ONE side))

theorem block_eq_literal (low : Low) (extra : Extra) (a b : Nat → R) (c : R)
    (hlow : ∀ s, s<16 → A.decodeE (lookup low field.wide_exact.WideExact.ZERO s)=CuSavingsLibra.literalLow a b c s)
    (j : Nat) :
    block A low extra j=CuSavingsLibra.literalBlock a b c (challenge A extra 0) (challenge A extra 1) j := by
  unfold block partialSum CuSavingsLibra.literalBlock CuSavingsLibra.sumRange
  congr 1
  apply List.map_congr_left
  intro s hs
  have hslot : s<16 := List.mem_range.mp hs
  unfold term CuSavingsLibra.literalCell
  by_cases hactive : 16*j+s<56
  · simp only [hactive,if_pos,hlow s hslot,map_pow]
    by_cases hzero : (16*j+s)/28=0
    · simp only [hzero,if_pos,challenge]
    · have hone : (16*j+s)/28=1 := by omega
      simp only [hone,show ¬(1:Nat)=0 by decide,if_false,challenge]
  · simp only [hactive,if_false]

theorem source_success (low : Low) (extra : Extra) (a b : Nat → R) (c : R)
    (hlowC : ∀ s, s<16 → A.canonicalE (lookup low field.wide_exact.WideExact.ZERO s))
    (hextra : ∀ side, side<2 → A.canonicalK (lookup extra field.QM31.ONE side))
    (hlowV : ∀ s, s<16 → A.decodeE (lookup low field.wide_exact.WideExact.ZERO s)=CuSavingsLibra.literalLow a b c s) :
    ∃ weights : Array E 4#usize,old.twofold_libra_weights low extra=.ok weights ∧
      ∀ j,j<4 → A.canonicalE (lookup weights field.wide_exact.WideExact.ZERO j) ∧
        A.decodeE (lookup weights field.wide_exact.WideExact.ZERO j)=
          CuSavingsLibra.literalBlock a b c (challenge A extra 0) (challenge A extra 1) j := by
  obtain ⟨weights,hweights,hvalues⟩ := CuSavingsLibraReference.source_success A low extra hlowC hextra
  refine ⟨weights,hweights,?_⟩
  intro j hj
  obtain ⟨hc,hv⟩ := hvalues j hj
  exact ⟨hc,hv.trans (block_eq_literal A low extra a b c hlowV j)⟩

#print axioms block_eq_literal
#print axioms source_success
end AspisR1.CuSavingsLibraReferenceLiteral
