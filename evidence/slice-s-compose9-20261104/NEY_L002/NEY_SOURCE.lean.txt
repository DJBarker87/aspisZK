import KMX_CopyMeaning
set_option autoImplicit false
namespace NEY_ResultWindows

/-- The frozen result encoder's nine disjoint output windows. Each source is
indexed by its absolute destination offset, as in an arbitrary-byte native cut.
This is a value law only; native argument/error/ownership laws are separate. -/
def run {α : Type} (source before : Nat → α) : Nat → α :=
  let a := KMX_CopyMeaning.loop source before 0 4
  let b := KMX_CopyMeaning.loop source a 4 1
  let c := KMX_CopyMeaning.loop source b 5 1
  let d := KMX_CopyMeaning.loop source c 6 1
  let e := KMX_CopyMeaning.loop source d 7 1
  let f := KMX_CopyMeaning.loop source e 8 32
  let g := KMX_CopyMeaning.loop source f 40 32
  let h := KMX_CopyMeaning.loop source g 72 32
  KMX_CopyMeaning.loop source h 104 688

/-- Nine independent byte checks cover the complete 792-byte result. -/
theorem complete {α : Type} (source before : Nat → α) (k : Nat) (inside : k<792) :
    run source before k = source k := by
  simp only [run,KMX_CopyMeaning.loop_spec]
  all_goals repeat (first | rfl | (split <;> try omega))

/-- Every cell outside the complete buffer retains its arbitrary pre-state. -/
theorem frame {α : Type} (source before : Nat → α) (k : Nat) (outside : 792≤k) :
    run source before k = before k := by
  simp only [run,KMX_CopyMeaning.loop_spec]
  all_goals repeat (first | rfl | (split <;> try omega))

/-- The final afterstate copy cannot change any previously established field. -/
theorem suffix_frame {α : Type} (source before : Nat → α) (k : Nat) (beforeSuffix : k<104) :
    KMX_CopyMeaning.loop source before 104 688 k = before k :=
  KMX_CopyMeaning.copy_frame source before 104 688 k (Or.inl beforeSuffix)

#print axioms complete
#print axioms frame
#print axioms suffix_frame
end NEY_ResultWindows
