import NGM_DoubleModel
set_option autoImplicit false
namespace NGW_WordExt
open Aeneas Aeneas.Std Result
abbrev Q := FIn_WeightsExtract.field.QM31
abbrev words := NGM_DoubleModel.words

theorem word_injective : Function.Injective words := by
 intro x y same
 rcases x with ⟨⟨a,b⟩,⟨c,d⟩⟩
 rcases y with ⟨⟨e,f⟩,⟨g,h⟩⟩
 have values := congrArg (fun a : Array U32 4#usize=>a.val) same
 simp only [words,NGM_DoubleModel.words,Array.make,List.cons.injEq,eq_self_iff_true,and_true] at values
 rcases values with ⟨rfl,rfl,rfl,rfl⟩
 rfl

theorem array_ext {α : Type} {n : Usize} (a b : Array α n)
    (same : ∀ (i : Nat) (ha : i<a.val.length) (hb : i<b.val.length),a.val[i]=b.val[i]) : a=b := by
 apply Subtype.ext
 apply List.ext_getElem
 · rw [a.property,b.property]
 · exact same

theorem words_ext {n : Usize} (a b : Array Q n)
    (same : ∀ (i : Nat) (ha : i<a.val.length) (hb : i<b.val.length),
       words a.val[i]=words b.val[i]) : a=b := by
 apply array_ext a b
 intro i ha hb
 exact word_injective (same i ha hb)

#print axioms word_injective
#print axioms array_ext
#print axioms words_ext
end NGW_WordExt
