import MultiproofParserRef.Funs

set_option autoImplicit false
namespace AspisR1.MultiproofConeWordScan
open Aeneas Aeneas.Std Result
open MultiproofParserRef

def wordsModel : List U8 → Bool
  | [] => true
  | a::b::c::d::rest =>
      decide ((core.num.U32.from_le_bytes (Array.make 4#usize [a,b,c,d])).val < 2147483647) &&
        wordsModel rest
  | _ => false

/-- Total recursion over arbitrary stored slices. The recurrence never
normalizes a concrete proof-sized list. The byte-order identification with
the frozen parser's `little` remains a separate codec lemma. -/
theorem words_total (bytes : Slice U8) :
    parser_reference.canonical_words bytes = ok (wordsModel bytes.val) := by
  generalize hn : bytes.val.length = n
  induction n using Nat.strong_induction_on generalizing bytes with
  | h n ih =>
    rcases bytes with ⟨xs,bound⟩
    cases xs with
    | nil => rw [parser_reference.canonical_words]; rfl
    | cons a xs =>
      cases xs with
      | nil => rw [parser_reference.canonical_words]; rfl
      | cons b xs =>
        cases xs with
        | nil => rw [parser_reference.canonical_words]; rfl
        | cons c xs =>
          cases xs with
          | nil => rw [parser_reference.canonical_words]; rfl
          | cons d xs =>
            let tail : Slice U8 := ⟨xs, by scalar_tac⟩
            have ht := ih xs.length (by simp only [List.length_cons] at hn; omega) tail rfl
            have hn0 : n ≠ 0 := by simp only [List.length_cons] at hn; omega
            rw [parser_reference.canonical_words]
            simp only [core.slice.Slice.is_empty, Slice.length, hn, hn0, List.length_cons,
              Nat.succ_ne_zero, decide_false, bind_tc_ok, Bool.false_eq_true, if_false]
            have hb : ¬ Slice.len (⟨a::b::c::d::xs,bound⟩ : Slice U8) < 4#usize := by
              change ¬ (a::b::c::d::xs).length < 4
              simp only [List.length_cons]; omega
            simp only [hb, if_false]
            simp only [Slice.index_usize, Slice.getElem?_Usize_eq,
              List.getElem?_cons_zero, List.getElem?_cons_succ, bind_tc_ok]
            simp only [show (0#usize).val = 0 from rfl, show (1#usize).val = 1 from rfl, show (2#usize).val = 2 from rfl, show (3#usize).val = 3 from rfl, show (4#usize).val = 4 from rfl,
              List.getElem?_cons_zero, List.getElem?_cons_succ, bind_tc_ok]
            simp only [reference.canonical_word, lift, bind_tc_ok, decide_eq_true_eq, UScalar.lt_equiv,
              show (2147483647#u32).val = 2147483647 from rfl]
            split
            · simp only [core.slice.index.Slice.index,
                core.slice.index.SliceIndexRangeFromUsizeSlice,
                core.slice.index.SliceIndexRangeFromUsizeSlice.index]
              simp only [show (4#usize).val = 4 from rfl,
                show 4 ≤ (a::b::c::d::xs).length by simp,
                if_true, bind_tc_ok]
              change parser_reference.canonical_words tail = ok _
              simpa only [wordsModel, show decide ((core.num.U32.from_le_bytes (Array.make 4#usize [a,b,c,d])).val < 2147483647) = true from decide_eq_true (by assumption), Bool.true_and] using ht
            · simp_all only [wordsModel, decide_false, Bool.false_and]

#print axioms words_total
end AspisR1.MultiproofConeWordScan
