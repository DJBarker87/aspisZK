import NKY_LevelsLiteral
set_option autoImplicit false
noncomputable section
namespace AspisR1.NKY_LevelsStep
open Aeneas Aeneas.Std Result ControlFlow
open NJX_AppendDomains (Frontier High)
open NJX_DigestCohort (O)
open FIv_NativeArithmetic (NQ)
open NJX_AppendFold (State)
open NKY_LevelCarrier (Pair pair state)
open NKY_LevelsLiteral (Child body)

theorem pair_values (s : State) :
 pair s=(Array.make 2#usize [s 0,s 1] (by simp only [List.length_cons,List.length_nil];rfl),
         Array.make 2#usize [s 2,s 3] (by simp only [List.length_cons,List.length_nil];rfl)) := by
 rfl

/-- Full literal four-add/update segment, arbitrary complete pre-state. -/
theorem arithmetic (before child : State) (level : Usize) :
 (do
  let q1 ← Array.index_usize (pair before).1 0#usize
  let q2 ← Array.index_usize (pair child).1 0#usize
  let q3 ← FIq_Native.field.QM31.add q1 q2
  let local01 ← Array.update (pair before).1 0#usize q3
  let q4 ← Array.index_usize local01 1#usize
  let q5 ← Array.index_usize (pair child).1 1#usize
  let q6 ← FIq_Native.field.QM31.add q4 q5
  let a1 ← Array.update local01 1#usize q6
  let q7 ← Array.index_usize (pair before).2 0#usize
  let q8 ← Array.index_usize (pair child).2 0#usize
  let q9 ← FIq_Native.field.QM31.add q7 q8
  let local121 ← Array.update (pair before).2 0#usize q9
  let q10 ← Array.index_usize local121 1#usize
  let q11 ← Array.index_usize (pair child).2 1#usize
  let q12 ← FIq_Native.field.QM31.add q10 q11
  let a2 ← Array.update local121 1#usize q12
  let next ← level+1#usize
  ok (cont (a1,a2,next)) : Result (ControlFlow (Array NQ 2#usize × Array NQ 2#usize × Usize) Pair))=
 (do let middle ← NJX_AppendFold.step before child
     let next ← level+1#usize
     ok (cont ((pair middle).1,(pair middle).2,next))) := by
 simp only [pair_values,Array.index_usize,Array.getElem?_Usize_eq,Array.update,Array.make,
  show (0#usize).val=0 from rfl,show (1#usize).val=1 from rfl,
  List.getElem?_cons_zero,List.getElem?_cons_succ,List.getElem?_nil,
  List.set_cons_zero,List.set_cons_succ,bind_tc_ok,NJX_AppendFold.step,bind_assoc_eq]
 rfl
#print axioms pair_values
#print axioms arithmetic
end AspisR1.NKY_LevelsStep
end
