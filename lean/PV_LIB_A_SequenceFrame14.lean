import PV_LIB_A_ExpressionFrame14
import PV_LIB_A_SourceSequence13
set_option autoImplicit false
noncomputable section
namespace PV_LIB_A_SequenceFrame14
open PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine PV_EVHB_OwnerMachine
open PV_LIB_A_SourceCellFrame14 PV_LIB_A_SourceSequence13

/-- Both the primary evaluator and the aggregate fallback frame SOURCE cells.
The fallback's value shape is not assumed to succeed. -/
theorem bound_frame (C : Carrier OWNER Data) (limit : Nat) (s t : Store Data)
    (w : OWNER) (a : Nat) (dest : PV_STX2_Syntax.Place) (e : Expr) (later : limit ≤ a)
    (own : Local dest) (safe : PV_LIB_A_ExpressionFrame14.Safe e)
    (evaluated : bound C s a dest e w = some t) : Below limit s t := by
  unfold bound PV_THR2_IntrinsicFrameChain.bound at evaluated
  cases first : PV_STX2_Store.bind C s w a dest e with
  | none =>
    simp only [first,Option.orElse] at evaluated
    exact PV_LIB_A_ExpressionFrame14.bind_frame _ limit s t w a dest e later own safe evaluated
  | some u =>
    simp only [first,Option.orElse] at evaluated
    cases evaluated
    exact PV_LIB_A_ExpressionFrame14.bind_frame C limit s t w a dest e later own safe first

def storeOf : Status → Store Data
  | .running c => c.store
  | .returned _ s | .fault _ s | .undefined _ s => s

def Safe : Seq → Prop
  | .done => True
  | .storage _ _ _ tail => Safe tail
  | .bind _ dest e tail => Local dest ∧ PV_LIB_A_ExpressionFrame14.Safe e ∧ Safe tail
  | .aggregate _ dest kind args tail => Local dest ∧ PV_LIB_A_ExpressionFrame14.Safe (.aggregate kind args) ∧ Safe tail

/-- Every failed-binding status is included in this SOURCE frame theorem.
No completed read, decoder success or native answer is assumed. -/
theorem result_frame (C : Carrier OWNER Data) (limit : Nat) (s : Store Data)
    (a : Nat) (parents : List Frame) (loops : List LoopFrame)
    (rest : List PV_STX2_SliceSyntax.Node) (w : OWNER) (seq : Seq)
    (later : limit ≤ a) (safe : Safe seq) :
    Below limit s (storeOf (result C a parents loops rest w seq s)) := by
  induction seq generalizing s with
  | done => exact refl limit s
  | storage site live slot tail ih =>
    exact trans limit s (write s ⟨a,slot,[]⟩ none) _
      (write_frame limit s ⟨a,slot,[]⟩ none later) (ih _ safe)
  | bind site dest e tail ih =>
    cases h : bound C s a dest e w with
    | none => simpa only [result,h,storeOf] using refl limit s
    | some t =>
      simp only [result,h]
      exact trans limit s t _ (bound_frame C limit s t w a dest e later safe.1 safe.2.1 h)
        (ih t safe.2.2)
  | aggregate site dest kind args tail ih =>
    cases h : bound C s a dest (.aggregate kind args) w with
    | none => simpa only [result,h,storeOf] using refl limit s
    | some t =>
      simp only [result,h]
      exact trans limit s t _ (bound_frame C limit s t w a dest (.aggregate kind args) later safe.1 safe.2.1 h)
        (ih t safe.2.2)

#print axioms bound_frame
#print axioms storeOf
#print axioms Safe
#print axioms result_frame
end PV_LIB_A_SequenceFrame14
