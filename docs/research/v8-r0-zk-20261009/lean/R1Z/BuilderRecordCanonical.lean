import R1Z.BuilderCanonical

/-! Lossless decoding of all raw witness fields. The range conditions are
explicit caller obligations; this does not infer them from Rust admission. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.BuilderRecordCanonical
open Aeneas Aeneas.Std R0Z.WriterRefine R0Z.BuilderModel
open R1J.SpendWitnessMap

structure CanonicalWords (w : RustWitness) : Prop where
  shape : WitnessOk w
  sk : Canon8 w.sk
  salt : Canon8 w.salt
  pairFirst : Canon8 w.pairFirst
  pairOccupied : w.pairOccupied.val < 2147483647
  pairSecond : Canon8 w.pairSecond
  pairInverse : w.pairInverse.val < 2147483647
  recipientOwner : Canon8 w.recipientOwner
  recipientSalt : Canon8 w.recipientSalt
  changeOwner : Canon8 w.changeOwner
  changeSalt : Canon8 w.changeSalt

theorem array_ext {α : Type} [Inhabited α] {n : Usize} (a b : Array α n)
    (h : ∀ i, i < n.val → a.val[i]! = b.val[i]!) : a = b := by
  apply Subtype.ext
  apply List.ext_getElem (a.property.trans b.property.symm)
  intro i hi hj
  simpa only [getElem!_pos a.val i hi, getElem!_pos b.val i hj] using
    h i (by simpa only [a.property] using hi)

theorem word_roundtrip (x : U32) (hx : x.val < 2147483647) :
    w32 (liftU (K := F) x) = x := by
  apply UScalar.eq_of_val_eq
  rw [w32_val]
  change (x.val : ZMod 2147483647).val = x.val
  rw [ZMod.val_natCast, Nat.mod_eq_of_lt hx]

theorem value_roundtrip (x : U32) (hx : x.val < 2^30) :
    v32 (val30 x) = x := by
  apply UScalar.eq_of_val_eq
  rw [v32_val]
  exact Nat.mod_eq_of_lt hx

theorem digest_roundtrip (d : Array U32 8#usize) (hd : Canon8 d) :
    d32 (digK (K := F) d) = d := by
  apply array_ext
  intro i hi
  rw [d32, arr8_get _ i (by simpa using hi)]
  exact word_roundtrip _ (hd i (by simpa using hi))

/-- Every one of the fifteen raw witness fields is retained, with no modular
aliasing of values, direction bits, pair coordinates or digest limbs. -/
theorem records_roundtrip (w : RustWitness) (hw : CanonicalWords w) :
    toRust (toModel (K := F) w) = w := by
  unfold toRust toModel
  congr 1
  · exact value_roundtrip _ hw.shape.values.1
  · exact value_roundtrip _ hw.shape.values.2.1
  · exact value_roundtrip _ hw.shape.values.2.2
  · exact digest_roundtrip _ hw.sk
  · exact digest_roundtrip _ hw.salt
  · apply array_ext
    intro i hi
    rw [R1J.SpendWitnessMap.arr24_get _ i (by simpa using hi)]
    apply UScalar.eq_of_val_eq
    change (if decide ((w.bits.val[i]!).val ≠ 0) then 1#u32 else 0#u32).val =
      (w.bits.val[i]!).val
    obtain hz | ho := hw.shape.bits i (by simpa using hi)
    · rw [hz]; rfl
    · rw [ho]; rfl
  · apply array_ext
    intro i hi
    rw [R1J.SpendWitnessMap.arr24_get _ i (by simpa using hi)]
    exact digest_roundtrip _ (hw.shape.sibs i (by simpa using hi))
  · exact digest_roundtrip _ hw.pairFirst
  · exact word_roundtrip _ hw.pairOccupied
  · exact digest_roundtrip _ hw.pairSecond
  · exact word_roundtrip _ hw.pairInverse
  · exact digest_roundtrip _ hw.recipientOwner
  · exact digest_roundtrip _ hw.recipientSalt
  · exact digest_roundtrip _ hw.changeOwner
  · exact digest_roundtrip _ hw.changeSalt

/-- The semantic witness read from the raw records, including the first
commitment (which is not discarded by modelWitness). -/
def witness (w : RustWitness) : AspisR1.SpendRelation.Wspend :=
  let m := toModel (K := F) w
  { inputValue := m.inputValue, outputValue := m.outputValue, changeValue := m.changeValue,
    sk := m.sk, salt := m.salt, path := m.path,
    pair := ⟨m.pairFirst, m.pairOccupied, m.pairSecond, m.pairInverse⟩,
    recipientOwner := m.recipientOwner, recipientSalt := m.recipientSalt,
    changeOwner := m.changeOwner, changeSalt := m.changeSalt }

theorem witness_model (w : RustWitness) :
    BuilderSpendRelation.modelWitness (witness w) = toModel (K := F) w := rfl

theorem canonical_witness (w : RustWitness) (hw : CanonicalWords w) :
    BuilderCanonical.rustWitness (witness w) = w := records_roundtrip w hw

#print axioms array_ext
#print axioms word_roundtrip
#print axioms value_roundtrip
#print axioms digest_roundtrip
#print axioms records_roundtrip
#print axioms witness_model
#print axioms canonical_witness
end R1Z.BuilderRecordCanonical
