import NJU_CurrentWindows
set_option autoImplicit false
noncomputable section
namespace NJU_BadWindow
open Aeneas Aeneas.Std Result AspisR1

/-- A fixed-length bad window identifies an actual noncanonical word. -/
theorem witness (bytes : Slice U8) (n : Nat) (size : bytes.val.length=32*n)
 (bad : ¬ NIG_FinishInput.Windows bytes n) :
 ∃ i, i<n ∧ ∃ j, j<8 ∧ 2147483647≤NIG_FinishInput.word bytes.val (32*i+4*j) := by
 by_contra missing
 apply bad
 refine ⟨size,?_⟩
 intro i hi j hj
 by_contra bound
 exact missing ⟨i,hi,j,hj,by omega⟩

/-- A noncanonical actual word cannot produce a returned field value. This
is universal, unlike a should_panic test. Failure/divergence classification
and whole-finish prefix transport are separate obligations. -/
theorem noncanonical (bytes : Slice U8) (i : Usize) (j : Fin 8)
 (fits : 32*i.val+32≤bytes.val.length)
 (bad : 2147483647≤NIG_FinishInput.word bytes.val (32*i.val+4*j.val)) :
 ∀ out, FIn_Primitives.field bytes i ≠ ok out := by
 intro out run
 have decoded:=FIn_Primitives.field_value bytes i out run
 have good:=NJR_DecodedWords.window bytes (32*i.val) fits _ decoded j
 omega

/-- Every successful emitted read has an in-bounds complete 32-byte window. -/
theorem read_bounds (bytes : Slice U8) (i : Usize)
 (value : AspisR1CurrentWide.Proof.FinishE)
 (run : AspisR1CurrentWide.Proof.finishField bytes i=ok value) :
 32*i.val+32≤bytes.val.length := by
 unfold AspisR1CurrentWide.Proof.finishField at run
 obtain ⟨record,fieldCall,_⟩:=F3P_ResultBind.success _ _ _ run
 obtain ⟨start,next,finish,selected,startEq,nextEq,finishPos,selectedCall,_⟩:=
  AspisR1WeightsFieldCurrent.WeightsFieldSuccess.checked_slice_decode _ bytes i record fieldCall
 have nextVal:=F3P_TraceArithmetic.checked_add i 1#usize next nextEq
 have finishVal:=F3P_TraceArithmetic.checked_mul next 32#usize finish finishPos
 have bounds:=PSem_Slices.range_bounds bytes selected start finish selectedCall
 change next.val=i.val+1 at nextVal
 change finish.val=next.val*32 at finishVal
 omega

/-- Short slices are rejected at the actual checked slice, before decoding. -/
theorem short (bytes : Slice U8) (i : Usize) (bad : bytes.val.length<32*i.val+32) :
 ∀ out, AspisR1CurrentWide.Proof.finishField bytes i ≠ ok out := by
 intro out run
 have bounds:=read_bounds bytes i out run
 omega

#print axioms witness
#print axioms noncanonical
#print axioms read_bounds
#print axioms short
end NJU_BadWindow
