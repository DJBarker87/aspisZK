import R1Z.BuilderRecordsReference

/-! Admission facts derived from the computed record map. These lemmas use
only the primitive range/canonical-sibling facts checked by the Rust caller;
they do not assume RspendPlus or builder soundness. -/
set_option autoImplicit false
namespace R1Z.BuilderRecordsAdmission
open Aeneas Aeneas.Std Result R0Z.WriterRefine
open BuilderRecordsReference BuilderRecordsArray

theorem bool_word (b : Bool) :
    (core.convert.num.FromU32Bool.from b).val = 0 ∨
      (core.convert.num.FromU32Bool.from b).val = 1 := by
  cases b <;> simp [core.convert.num.FromU32Bool.from]

theorem low_bit (x : U32) : (x &&& 1#u32).val = 0 ∨ (x &&& 1#u32).val = 1 := by
  have hb : x.val % 2 < 2 := Nat.mod_lt _ (by decide)
  simp only [UScalar.val_and, UScalar.ofNatCore_val_eq, Nat.and_one_is_mod]
  omega

theorem bits_boolean (input : Input) (l : Nat) (hl : l < 24) :
    ((BuilderRecordsPath.bits input).val[l]!).val = 0 ∨ ((BuilderRecordsPath.bits input).val[l]!).val = 1 := by
  let i : Usize := Usize.ofNatCore l (by
    simpa [UScalar.size_def] using lt_of_lt_of_le (by omega : l < 2^32) R0Z.WriterRefine.usize_size_ge)
  have hi : i.val = l := UScalar.ofNatCore_val_eq _
  have hg := BuilderRecordsPath.bits_get input i (by omega)
  rw [hi] at hg
  rw [hg]
  split
  · exact bool_word _
  · split
    · exact low_bit _
    · exact bool_word _

/-- No canonicality of key/owner/salt/pair words is required: only sibling
words are constrained by WitnessOk. Both selected pair siblings are admitted
by the pair-leaf validator; super-root siblings by the forest caller. -/
theorem witness_ok (input : Input) (out : U32) (rec : Option Note) (chg : Note)
    (values : input.pair.value.val < 2^30 ∧ out.val < 2^30 ∧ chg.value.val < 2^30)
    (first : Canon8 input.pair.pair_leaf.first_commitment)
    (second : Canon8 input.pair.pair_leaf.second_commitment)
    (membership : ∀ l, l < 20 → Canon8 input.pair.membership.siblings.val[l]!)
    (superRoot : ∀ l, l < 3 → Canon8 input.super_root_siblings.val[l]!) :
    WitnessOk (BuilderExtractedRecords.rawWitness (witness input out rec chg)) where
  values := values
  bits := bits_boolean input
  sibs := by
    intro l hl
    change Canon8 ((BuilderRecordsPath.siblings input).val[l]!)
    rw [BuilderRecordsPath.siblings, tabulate_get _ _ _ (by simpa using hl)]
    split
    · split
      · exact first
      · exact second
    · split
      · exact membership _ (by omega)
      · exact superRoot _ (by omega)

#print axioms bool_word
#print axioms low_bit
#print axioms bits_boolean
#print axioms witness_ok
end R1Z.BuilderRecordsAdmission
