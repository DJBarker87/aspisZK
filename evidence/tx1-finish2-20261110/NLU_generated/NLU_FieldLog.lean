import NLU_Words
import NLU_Cell
set_option autoImplicit false
namespace AspisR1.NLU_FieldLog
open Aeneas Aeneas.Std
open NLU (Q word cell)
structure Frame where
 eta : Q
 terminal : Q
 mask : Q
 extra : Q
structure Replies where
 product : Q
 partialValue : Q
 total : Q
structure Observation where
 calls : Nat
 args : Array (Q×Q) 3#usize
 returned : Q
abbrev Native := Frame → Replies → Observation
def arguments (f : Frame) (r : Replies) (i : Fin 3) : Q×Q :=
 if i.val=0 then (f.eta,f.terminal)
 else if i.val=1 then (f.mask,r.product) else (r.partialValue,f.extra)
/-- programs/r1-cost-probe/src/NLU_program.rs SHA256
081a7249e92a16f46461172a7cb5f84a8c36a092e218408cb3dfd018226aea8c. Literal assertion:
"log.calls==3 && word(actual,limb)==word(expected,limb) &&
word(masked,limb)==word(replies[2],limb)" (K023/K024).
Exact transcription of the planned local-record arithmetic_arguments
native assertions: count3, arbitrary selected call/operand/word, and returned
word. The three replies are independent. No multiplication specification or
canonicality is silently added; those remain separate Lean obligations. -/
def Cut (native : Native) : Prop := ∀ f r,
 (native f r).calls=3 ∧
 (∀ i : Fin 3,∀ j : Fin 4,
   word (cell (native f r).args i.val i.isLt).1 j=word (arguments f r i).1 j ∧
   word (cell (native f r).args i.val i.isLt).2 j=word (arguments f r i).2 j) ∧
 (∀ j,word (native f r).returned j=word r.total j)
theorem operands (native : Native) (cut : Cut native) (f : Frame) (r : Replies) (i : Fin 3) :
 cell (native f r).args i.val i.isLt=arguments f r i := by
 apply Prod.ext
 · exact NLU.word_ext _ _ (fun j=>(cut f r).2.1 i j |>.1)
 · exact NLU.word_ext _ _ (fun j=>(cut f r).2.1 i j |>.2)
theorem returned (native : Native) (cut : Cut native) (f : Frame) (r : Replies) :
 (native f r).returned=r.total := NLU.word_ext _ _ (cut f r).2.2
/-- Native call-log reassembly only, never an arithmetic or136 root. -/
theorem complete (native : Native) (cut : Cut native) (f : Frame) (r : Replies) :
 (native f r).calls=3 ∧ (∀ i : Fin 3,cell (native f r).args i.val i.isLt=arguments f r i) ∧
 (native f r).returned=r.total :=
 ⟨(cut f r).1,operands native cut f r,returned native cut f r⟩
#print axioms operands
#print axioms returned
#print axioms complete
end AspisR1.NLU_FieldLog
