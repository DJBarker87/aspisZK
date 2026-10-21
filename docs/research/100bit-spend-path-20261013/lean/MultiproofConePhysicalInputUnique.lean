import MultiproofConePhysicalNode

set_option autoImplicit false
namespace AspisR1.MultiproofConePhysicalInputUnique
open Aeneas Aeneas.Std MultiproofConeRef
open MultiproofConePhysicalNode MultiproofConeLiveReference

/-- Actual child order, next input cursor and physical sibling cursor are
uniquely fixed BEFORE the oracle answer. The digest is not a premise here. -/
theorem input_unique (physical : Slice U8) (s : reference.Scratch) (i : Usize)
    (left right left' right' : Array U8 32#usize) (ni cursor ni' cursor' : Usize)
    (first : Input physical s i left right ni cursor)
    (second : Input physical s i left' right' ni' cursor') :
    left=left' ∧ right=right' ∧ ni=ni' ∧ cursor=cursor' := by
  unfold Input at first second
  by_cases pair : SourcePair s i
  · simp only [pair,if_true] at first second
    exact ⟨first.1.trans second.1.symm,first.2.1.trans second.2.1.symm,
      UScalar.eq_of_val_eq (first.2.2.1.trans second.2.2.1.symm),
      first.2.2.2.trans second.2.2.2.symm⟩
  · simp only [pair,if_false] at first second
    obtain ⟨sib,bytes,children,advance,cursorVal⟩ := first
    obtain ⟨sib',bytes',children',advance',cursorVal'⟩ := second
    have eq : sib=sib' := Subtype.ext (bytes.trans bytes'.symm)
    subst sib'
    by_cases even : s.idx.val[i.val]!.val%2=0
    all_goals simp only [even,if_true,if_false] at children children'
    all_goals exact ⟨children.1.trans children'.1.symm,children.2.trans children'.2.symm,
      UScalar.eq_of_val_eq (advance.trans advance'.symm),UScalar.eq_of_val_eq (cursorVal.trans cursorVal'.symm)⟩

#print axioms input_unique
end AspisR1.MultiproofConePhysicalInputUnique
