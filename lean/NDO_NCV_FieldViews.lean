import NDO_NCV_CastHelpers
import MultiproofConeSlices
set_option autoImplicit false
namespace NCV_FieldViews
open Aeneas Aeneas.Std Result AspisR1

theorem nested (b : Slice U8) (a n s w : Nat) (fit : s+w ≤ n) :
    JHg_FieldRead.segment (JHg_FieldRead.segment b a n) s w=
      JHg_FieldRead.segment b (a+s) w := by
  apply Subtype.ext
  simp only [JHg_FieldRead.segment,List.drop_take,List.drop_drop,List.take_take]
  have h : w ≤ n-s := by omega
  simp only [Nat.min_eq_left h]

theorem read_prefix (b : Slice U8) (n : Usize) (fit : n.val ≤ b.val.length) :
    core.slice.index.Slice.index (core.slice.index.SliceIndexRangeToUsizeSlice U8)
      b {«end»:=n}=ok (JHg_FieldRead.segment b 0 n.val) := by
  have same : MultiproofConeSlices.sub b 0#usize n=JHg_FieldRead.segment b 0 n.val := by
    apply Subtype.ext
    simp only [MultiproofConeSlices.sub,JHg_FieldRead.segment,show (0#usize).val=0 from rfl,Nat.sub_zero]
  simpa only [same] using MultiproofConeSlices.prefix_total b n fit

theorem suffix (b : Slice U8) (s : Usize) :
    Slice.drop b s=JHg_FieldRead.segment b s.val (b.val.length-s.val) := by
  apply Subtype.ext
  change b.val.drop s.val=(b.val.drop s.val).take (b.val.length-s.val)
  have same : (b.val.drop s.val).take (b.val.drop s.val).length=b.val.drop s.val := List.take_length
  simpa only [List.length_drop] using same.symm

theorem byte (b : Slice U8) (i : Usize) (x : U8) (fit : i.val<b.val.length)
    (field : (b.val.drop i.val).take 1=[x]) : Slice.index_usize b i=ok x := by
  have value:=congrArg (fun xs : List U8=>xs[0]?.getD 0#u8) field
  have same : NCV_ZeroStep.byte b i.val=x := by
    simpa [NCV_ZeroStep.byte] using value
  rw [NCV_ZeroStep.read b i fit,same]

#print axioms nested
#print axioms read_prefix
#print axioms suffix
#print axioms byte
end NCV_FieldViews
