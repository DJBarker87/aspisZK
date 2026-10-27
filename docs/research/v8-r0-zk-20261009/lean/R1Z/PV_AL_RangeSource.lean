import R1Z.PV_AL_RangeLoop
open Aeneas Aeneas.Std Result
namespace R1Z.PV_AL_RangeSource
set_option autoImplicit false

theorem source (v : Slice U8) (first last : Usize) (out : alloc.vec.Vec U8)
    (hl : last.val ≤ v.val.length) (hi : first.val ≤ last.val) (empty : out.val=[]) :
    ∃ a, PV_AL_SplitFlat.copy_range v first last out=ok a ∧
      a.val=PV_AL_RangeLists.segment v.val first.val last.val := by
  apply PV_AL_RangeLoop.source v out first.val last first hl hi (Nat.le_refl _)
  rw [PV_AL_RangeLists.zero]
  exact empty

theorem empty_initial (v : Slice U8) (first last : Usize)
    (hl : last.val ≤ v.val.length) (hi : first.val ≤ last.val) :
    ∃ a, PV_AL_SplitFlat.copy_range v first last (alloc.vec.Vec.new U8)=ok a ∧
      a.val=PV_AL_RangeLists.segment v.val first.val last.val :=
  source v first last _ hl hi rfl

#print axioms source
#print axioms empty_initial
end R1Z.PV_AL_RangeSource
