import NGW_StepModel
set_option autoImplicit false
namespace NGW_ReverseInduction
open Aeneas Aeneas.Std Result ControlFlow NGW_ConstructorQM NGW_Reverse

def reference : Nat → Rev → Array Q 10#usize → Array Q 10#usize → Q → Result (Array Q 10#usize)
 | 0,_,_,successor,_ => ok successor
 | n+1,iter,z,successor,carry => do
   let (o,cursor) ← next iter
   match o with
   | none => ok successor
   | some i =>
     let (out,product) ← NGW_StepModel.step z successor carry i
     reference n cursor z out product

theorem source (n : Nat) (z successor : Array Q 10#usize) (carry : Q)
    (e : Usize) (bound : e.val≤n) :
 FIn_WeightsExtract.state_only_prefix.state_only_statement_points_loop (cursor e) z successor carry =
 reference n (cursor e) z successor carry := by
 induction n generalizing e successor carry with
 | zero =>
   have ez : e=0#usize := UScalar.eq_of_val_eq (by omega)
   subst e
   unfold FIn_WeightsExtract.state_only_prefix.state_only_statement_points_loop
   rw [loop.eq_def]
   simp only [FIn_WeightsExtract.state_only_prefix.state_only_statement_points_loop.body,
     show core.iter.adapters.rev.Rev.Insts.CoreIterTraitsIteratorIterator.next
       (core.ops.range.Range.Insts.DoubleEndedIterator core.iter.range.StepUsize) (cursor 0#usize)=
       ok (none,cursor 0#usize) from stop,bind_tc_ok,reference]
 | succ n ih =>
   by_cases zero : e.val=0
   · have ez : e=0#usize := UScalar.eq_of_val_eq zero
     subst e
     unfold FIn_WeightsExtract.state_only_prefix.state_only_statement_points_loop
     rw [loop.eq_def]
     simp only [FIn_WeightsExtract.state_only_prefix.state_only_statement_points_loop.body,
       show core.iter.adapters.rev.Rev.Insts.CoreIterTraitsIteratorIterator.next
         (core.ops.range.Range.Insts.DoubleEndedIterator core.iter.range.StepUsize) (cursor 0#usize)=
         ok (none,cursor 0#usize) from stop,bind_tc_ok,reference,next,stop]
   · obtain ⟨j,decrease,advance⟩ := step e (by omega)
     conv_lhs => unfold FIn_WeightsExtract.state_only_prefix.state_only_statement_points_loop
     rw [loop.eq_def,NGW_StepModel.iteration z successor carry _ _ j advance]
     simp only [reference,advance,bind_tc_ok,bind_assoc_eq]
     cases run : NGW_StepModel.step z successor carry j with
     | fail error => rfl
     | div => rfl
     | ok pair =>
       rcases pair with ⟨out,product⟩
       simp only [bind_tc_ok]
       exact ih out product j (by omega)

#print axioms source
end NGW_ReverseInduction
