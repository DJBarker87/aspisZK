import NKI_InitialPrefix
import NJB_ArrayCarrier
import NLH_FoldRust
import NKR_TermPublic
import NKR_TermTail
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLH_WrapperState
open Aeneas Aeneas.Std Result FIq_Native
open FIv_NativeArithmetic (NQ)
open pool_v1.pair_forest_semantic_terminal
abbrev Claims := Array (Array NQ 29#usize) 3#usize
abbrev Challenges := state_only_prefix.r0.Challenges
abbrev Error := state_only_prefix.r0.Error
structure State where
 selected : Array NQ 84#usize
 public : SemanticPublic
 parts : NKR_TermTail.Output
inductive Event where
 | gather (i : Fin 84)
 | semantic
 | parts
def selectedCell (claims : Claims) (i : Fin 84) : NQ :=
 let row := claims.val[i.val/28]'(by rw [claims.property];change i.val/28 < 3;omega)
 row.val[i.val%28]'(by rw [row.property];change i.val%28 < 29;have h:=Nat.mod_lt i.val (by decide : 0<28);omega)
def step (pub : r0.Public) (claims : Claims) (point : Array NQ 10#usize)
 (c : Challenges) : Event → State → Result (core.result.Result State Error)
 | .gather i, st => ok (.Ok {st with selected := (NJB_ArrayCarrier.array
     (fun j => if j=i then selectedCell claims i else NJB_ArrayCarrier.cell st.selected j))})
 | .semantic, st => do
   let public ← pub.semantic
   ok (.Ok {st with public := public})
 | .parts, st => do
   let r ← terminal_parts st.public st.selected point c.lambda c.chi c.theta c.zc c.mu
   match r with
   | .Err _ => ok (.Err .Public)
   | .Ok parts => ok (.Ok {st with parts := parts})
def order : List Event := (List.finRange 84).map Event.gather ++ [.semantic,.parts]
def returned (st : State) : NQ := st.parts.1
/-- Model-side instantiation of the already CLOSED semantic255 projection at
this public input; the arbitrary initial public field cannot replace it. -/
theorem semantic_step (pub : r0.Public) (claims : Claims) (point : Array NQ 10#usize)
 (c : Challenges) (st : State) :
 step pub claims point c .semantic st=ok (.Ok {st with public := NKR_TermPublic.value pub}) := by
 simp only [step,NKR_TermPublic.source,bind_tc_ok]
#print axioms semantic_step
end AspisR1.NLH_WrapperState
end
