import NLT_NativeInvocation
set_option autoImplicit false
noncomputable section
namespace NLT_Reseed
open Aeneas Aeneas.Std Result AspisR1 VTop_Stages NJU_CommonObserved NKE_Free
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
/-- The exact same source continuation with different unused reply seeds.
Primitive std effects and call arguments are retained verbatim. -/
inductive Same {A : Type} : Program Event A → Program Event A → Prop where
 | ret (value : A) : Same (.ret value) (.ret value)
 | prim {B : Type} (reply : Result B) (left right : B → Program Event A)
   (tail : ∀ value,Same (left value) (right value)) : Same (.prim reply left) (.prim reply right)
 | call {B : Type} (codec : Codec Event B) (old fresh : Result B) (left right : B → Program Event A)
   (question : NLT_NativeWindows.question (codec.encode old)=NLT_NativeWindows.question (codec.encode fresh))
   (tail : ∀ value,Same (left value) (right value)) : Same (.call codec old left) (.call codec fresh right)
theorem source (wr rr wr' rr' : NP6_StdModel.Reservation) (merkle : Merkle) (finish finish' : Finish)
 {X : Type} (d : aspis_core.digest.Digest32 X) (pub proof ck : Slice U8) (hash : X) :
 Same (NKE_CommonProgram.run wr rr merkle finish d pub proof ck hash none)
  (NKE_CommonProgram.run wr' rr' merkle finish' d pub proof ck hash none) := by
 unfold NKE_CommonProgram.run
 repeat' first
 | (fail_if_no_progress dsimp only [Program.bind])
 | (apply Same.call)
 | (apply Same.prim)
 | (apply Same.ret)
 | (intro value)
 | rfl
 | (fail_if_no_progress dsimp only [NJU_Log.prod_cases])
 | split
set_option pp.proofs false
#print source
#print axioms source
end NLT_Reseed
