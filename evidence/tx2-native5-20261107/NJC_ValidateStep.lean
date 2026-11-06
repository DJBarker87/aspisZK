import NJC_Contains
import NJC_ValidateArithmetic
set_option autoImplicit false
noncomputable section
namespace NJC_ValidateStep
open Aeneas Aeneas.Std Result ControlFlow AspisR1

theorem source (q : Array U32 22#usize) (i : Usize)
 (pre tail : List U32) (x : U32)
 (shape : q.val=pre++x::tail) (index : i.val=pre.length) :
 NJC_ValidateEmission.verifier.validate_checkpoint_queries_loop.body q i=
 if x.val≥262144 ∨ x∈pre then ok (.done none)
 else ok (.cont (Usize.wrapping_add i 1#usize)) := by
 have room : i.val<q.val.length := by rw [shape,index];simp
 obtain ⟨value,read,equal⟩ := WP.spec_imp_exists (Array.index_usize_spec q i room)
 have valueEq : value=x := by rw [equal];simp [shape,index]
 have readX := read.trans (congrArg Result.ok valueEq)
 obtain ⟨front,frontRead,contents⟩ := Port5Q2_ReaderPrefix.read q i (by omega)
 have frontEq : front.val=pre := by rw [contents,shape,index];simp
 have active : i<Slice.len (Array.to_slice q) := by change i.val<q.val.length;exact room
 have small : i.val<22 := by have size : q.val.length=22 := q.property;omega
 simp only [NJC_ValidateEmission.verifier.validate_checkpoint_queries_loop.body,
  lift,bind_tc_ok,if_pos active,readX,NJC_ValidateArithmetic.shift]
 by_cases high : x.val≥262144
 · simp only [show x≥262144#u32 from high,ite_true,high,true_or]
 · simp only [show ¬x≥262144#u32 from high,ite_false,frontRead,bind_tc_ok]
   rw [NJC_Contains.source,frontEq]
   by_cases duplicate : x∈pre
   · simp [high,duplicate]
   · simp only [duplicate,decide_false, Bool.false_eq_true,if_false,
      NJC_ValidateArithmetic.increment i small,bind_tc_ok]
     simp only [high,false_or,duplicate,if_false]
#print axioms source
end NJC_ValidateStep
