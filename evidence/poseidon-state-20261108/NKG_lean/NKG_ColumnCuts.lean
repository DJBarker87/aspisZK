import NKG_ColumnReply
set_option autoImplicit false
noncomputable section
namespace AspisR1.NKG_ColumnCuts
open Aeneas Aeneas.Std Result FIq_Native
open FIv_NativeArithmetic (NQ)
open FJb_MatrixGroupStep (State)
open FJe_ThreeColumnStep (Weights)
open FJb_M31Step (Constants)
open FJb_TailCell (cell)
def word (q : NQ) (j : Fin 4) : U32 :=
 if j.val=0 then q.c0.a else if j.val=1 then q.c0.b else if j.val=2 then q.c1.a else q.c1.b
/-- K001/K002/K003: sampled arbitrary j<4 and k<16 assert all arguments,
all selected output words and every disjoint cell. K006/K007 cover exit.
P6/D188 reviewed cut transcription, not a model-value premise. -/
structure Step (w : Weights) (c0 c1 c2 : Constants) (s : State) (i : Fin 16)
 (reply : NQ) (out : State) (next calls : Nat) (args : Fin 4 → Fin 6 → U32) : Prop where
 increment : next=i.val+1
 callCount : calls=4
 arguments : ∀ j k, args j k =
   if h:k.val<3 then word (cell w ⟨k.val,h⟩) j
   else if k.val=3 then cell c0 i else if k.val=4 then cell c1 i else cell c2 i
 frame : out=s.set (Usize.ofNat i.val (by scalar_tac)) reply
/-- K008/K009 source ZERO initialization. The children are instantiated at
SAME reads by NKG_ColumnReply.result, under (y)(3)/(aq)(5). The only predicates
here are native cut assertions after that substitution; no child equation is
left as a field of a root hypothesis. -/
structure Trace (w : Weights) (c0 c1 c2 : Constants) (states : Nat → State) : Prop where
 initial : states 0=Array.repeat 16#usize field.QM31.ZERO
 steps : ∀ i : Fin 16, ∃ next calls args,
   Step w c0 c1 c2 (states i.val) i (NKG_ColumnReply.reply w c0 c1 c2 i)
     (states (i.val+1)) next calls args
#print Step
#print Trace
end AspisR1.NKG_ColumnCuts
end
