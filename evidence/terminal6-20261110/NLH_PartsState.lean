import NKI_InitialPrefix
import NJB_ArrayCarrier
import NLH_FoldRust
import NKR_TermTail
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLH_PartsState
open Aeneas Aeneas.Std Result FIq_Native
open FIv_NativeArithmetic (NQ)
open NKI_InitialPrefix (Public)
open pool_v1.pair_forest_semantic_terminal
structure State where
 child : NKR_TermTail.Carrier
 locals : Fin 9 → NQ
inductive Event where
 | composition
 | arithmetic (i : Fin 9)
def arithmetic (zc point : Array NQ 10#usize) (mu : NQ) (st : State) (i : Fin 9) : Result NQ :=
 match i.val with
 | 0 => equality_value zc point
 | 1 => field.QM31.mul (st.locals 0) st.child.1
 | 2 => field.QM31.mul mu st.child.2.2.2.2.1
 | 3 => field.QM31.add (st.locals 1) (st.locals 2)
 | 4 => field.QM31.mul mu mu
 | 5 => field.QM31.sub field.QM31.ONE st.child.2.2.2.2.2
 | 6 => field.QM31.mul (st.locals 5) st.child.2.2.2.2.1
 | 7 => field.QM31.mul (st.locals 4) (st.locals 6)
 | _ => field.QM31.add (st.locals 3) (st.locals 7)
def step (pub : Public) (claims : Array NQ 84#usize) (point zc : Array NQ 10#usize)
 (lambda chi theta mu : NQ) : Event → State → Result (core.result.Result State NKR_TermTail.Error)
 | .composition, st => do
   let result ← composition_parts pub claims point lambda chi theta
   match result with
   | .Err err => ok (.Err err)
   | .Ok child => ok (.Ok {st with child := child})
 | .arithmetic i, st => do
   let reply ← arithmetic zc point mu st i
   ok (.Ok {st with locals := fun j => if j=i then reply else st.locals j})
def order : List Event := [.composition] ++ (List.finRange 9).map Event.arithmetic
def returned (st : State) : NKR_TermTail.Output :=
 (st.locals 8,st.child.2.1,st.child.2.2.1,st.child.2.2.2.1)
/-- Native error-prefix cut K032/K033 has no arithmetic suffix. This is the
model instantiation at the SAME child argument, not a row-root premise. -/
theorem rejected (pub : Public) (claims : Array NQ 84#usize) (point zc : Array NQ 10#usize)
 (lambda chi theta mu : NQ) (st : State) (err : NKR_TermTail.Error)
 (h : composition_parts pub claims point lambda chi theta=ok (.Err err)) :
 NLH_FoldRust.run (step pub claims point zc lambda chi theta mu) order st=ok (.Err err) := by
 apply NLH_FoldRust.returned_error
 simp only [step,h,bind_tc_ok]
#print axioms rejected
end AspisR1.NLH_PartsState
end
