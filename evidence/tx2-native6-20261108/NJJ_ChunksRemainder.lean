import NJJ_Chunks
set_option autoImplicit false
namespace NJJ_ChunksRemainder

theorem offset (len width : Nat) (positive : 0<width) (fit : width≤len) :
 width+(len-width)/width*width=len/width*width := by
 have same : len=(len-width)+width := by omega
 have division : len/width=(len-width)/width+1 := by
  have d:=Nat.add_div_right (len-width) positive
  simpa only [←same] using d
 rw [division,Nat.add_mul,Nat.one_mul]
 omega

/-- Exact original incomplete byte suffix survives every complete next step.
This completes the remainder part of the hand ChunksExact library model. -/
theorem remainder_step {T : Type} (xs : List T) (width : Nat)
 (positive : 0<width) (fit : width≤xs.length) :
 NJJ_Chunks.remainder (⟨xs.drop width,width⟩ : NJJ_Chunks.State T)=
 NJJ_Chunks.remainder (⟨xs,width⟩ : NJJ_Chunks.State T) := by
 unfold NJJ_Chunks.remainder
 simp only [List.length_drop,List.drop_drop]
 congr 1
 exact offset xs.length width positive fit

#print axioms offset
#print axioms remainder_step
end NJJ_ChunksRemainder
