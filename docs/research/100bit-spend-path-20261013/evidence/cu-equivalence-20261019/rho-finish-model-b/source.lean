import AspisR1CuRho.Finish
import CuSavingsRhoValue
import CuSavingsSuffixOverwrite

/-! The exact canonical output and suffix overwrite invariant for finish.
The iterator interface's source admission remains a separate obligation. -/
set_option autoImplicit false
namespace AspisR1.CuSavingsRhoFinishModel
open Aeneas Aeneas.Std Result ControlFlow
open AspisR1CuRho
open AspisR1.CuSavingsRhoValue AspisR1.CuSavingsSuffixOverwrite
abbrev Iter := Aeneas.Std.core.slice.iter.IterMut field.QM31
abbrev Enum := Aeneas.Std.core.iter.adapters.enumerate.Enumerate Iter

def canonicalSlice (self : verifier.BatchedWeights) : Slice field.QM31 :=
  ⟨self.raw.val.map canonicalValue,by
    simpa only [List.length_map] using self.raw.property⟩

def modelIter (iter : Enum) (target : Slice field.QM31)
    (hlen : iter.iter.slice.val.length = target.val.length) : Enum :=
  {iter :=
    {slice := ⟨overwrite iter.iter.i iter.iter.slice.val target.val,by
       rw [length_overwrite _ _ _ hlen];exact iter.iter.slice.property⟩
     i := iter.iter.slice.val.length}
   count := iter.iter.slice.len}

theorem model_at_end (iter : Enum) (target : Slice field.QM31)
    (hlen : iter.iter.slice.val.length = target.val.length)
    (hend : iter.iter.i = iter.iter.slice.val.length)
    (hcount : iter.count.val = iter.iter.i) : modelIter iter target hlen = iter := by
  rcases iter with ⟨⟨values,position⟩,count⟩
  change position = values.val.length at hend
  change count.val = position at hcount
  subst position
  have hc : values.len = count := UScalar.eq_of_val_eq (by
    simpa only [Slice.length] using (Slice.len_val values).trans hcount.symm)
  unfold modelIter
  simp only [overwrite_at_length _ _ hlen,hc]

theorem model_step (iter : Enum) (target : Slice field.QM31)
    (hlen : iter.iter.slice.val.length = target.val.length)
    (hi : iter.iter.i < target.val.length) (count : Usize) :
    {modelIter {iter := {iter.iter with i := iter.iter.i+1},count := count} target hlen with
      iter := {(modelIter {iter := {iter.iter with i := iter.iter.i+1},count := count}
        target hlen).iter with
        slice := (modelIter {iter := {iter.iter with i := iter.iter.i+1},count := count}
          target hlen).iter.slice.setAtNat iter.iter.i (target.val[iter.iter.i]'hi)}} =
      modelIter iter target hlen := by
  rcases iter with ⟨⟨values,position⟩,oldCount⟩
  simp only [modelIter]
  congr 2
  apply Subtype.ext
  simp only [Slice.setAtNat]
  exact overwrite_step position values.val target.val hlen hi

#print axioms model_at_end
#print axioms model_step
end AspisR1.CuSavingsRhoFinishModel
