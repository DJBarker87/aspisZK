import NJU_Log
set_option autoImplicit false
noncomputable section
namespace NKE_Free
open Aeneas Aeneas.Std Result
/-- A site-specific decoder checks the SAME arguments and preserves the entire
reply. Its law is constructor inversion, not an assumed callee endpoint law. -/
structure Codec (E A : Type) where
 encode : Result A → E
 decode : E → Option (Result A)
 roundtrip : ∀ reply,decode (encode reply)=some reply

/-- Primitive std operations stay in the parent. Only entered child calls
consume a source-ordered log entry; continuations retain the complete frame. -/
inductive Program (E A : Type) : Type 1 where
 | ret (value : A)
 | prim {B : Type} (actual : Result B) (next : B → Program E A)
 | call {B : Type} (codec : Codec E B) (actual : Result B) (next : B → Program E A)

namespace Program
def bind {E A B : Type} (p : Program E A) (k : A → Program E B) : Program E B :=
 match p with
 | .ret value => k value
 | .prim actual next => .prim actual (fun value=>bind (next value) k)
 | .call codec actual next => .call codec actual (fun value=>bind (next value) k)

instance {E : Type} : Monad (Program E) where
 pure := .ret
 bind := bind

instance {E : Type} : MonadLift Result (Program E) where
 monadLift actual := .prim actual .ret
end Program

def record {E A : Type} (codec : Codec E A) (actual : Result A) : Program E A :=
 .call codec actual .ret

def eval {E A : Type} (p : Program E A) : NJU_Log.Run E A :=
 match p with
 | .ret value => ⟨.ok value,[]⟩
 | .prim actual next =>
   match actual with
   | .ok value => eval (next value)
   | .fail err => ⟨.fail err,[]⟩
   | .div => ⟨.div,[]⟩
 | .call codec actual next =>
   match actual with
   | .ok value => let after:=eval (next value)
                  ⟨after.result,codec.encode actual::after.events⟩
   | .fail err => ⟨.fail err,[codec.encode actual]⟩
   | .div => ⟨.div,[codec.encode actual]⟩

theorem eval_bind {E A B : Type} (p : Program E A) (k : A → Program E B) :
 eval (p >>= k)=(eval p >>= fun value=>eval (k value)) := by
 induction p with
 | ret value => rfl
 | prim actual next ih =>
  cases actual with
  | fail err => rfl
  | div => rfl
  | ok value => exact ih value
 | call codec actual next ih =>
  cases actual with
  | fail err => rfl
  | div => rfl
  | ok value =>
   change
    (⟨(eval (Program.bind (next value) k)).result,
      codec.encode (.ok value)::(eval (Program.bind (next value) k)).events⟩ : NJU_Log.Run E B)=
    NJU_Log.bind
     ⟨(eval (next value)).result,codec.encode (.ok value)::(eval (next value)).events⟩
     (fun value=>eval (k value))
   have recursive := ih value
   change eval (Program.bind (next value) k)=
    NJU_Log.bind (eval (next value)) (fun value=>eval (k value)) at recursive
   rw [recursive]
   cases h : eval (next value) with
   | mk result events => cases result <;> rfl

theorem eval_record {E A : Type} (codec : Codec E A) (actual : Result A) :
 eval (record codec actual)=NJU_Log.record codec.encode actual := by
 cases actual <;> rfl

theorem eval_liftM {E A : Type} (actual : Result A) :
 eval (liftM actual : Program E A)=(liftM actual : NJU_Log.Run E A) := by
 cases actual <;> rfl

theorem eval_pure {E A : Type} (value : A) :
 eval (pure value : Program E A)=(pure value : NJU_Log.Run E A) := rfl

theorem eval_if {E A : Type} (condition : Prop) [Decidable condition]
 (yes no : Program E A) :
 eval (if condition then yes else no)=if condition then eval yes else eval no := by
 split <;> rfl

theorem eval_flow {E A B C : Type} (flow : core.ops.control_flow.ControlFlow C B)
 (yes : B → Program E A) (no : C → Program E A) :
 eval (match flow with | .Continue value=>yes value | .Break residual=>no residual)=
 match flow with | .Continue value=>eval (yes value) | .Break residual=>eval (no residual) := by
 cases flow <;> rfl
#print axioms eval_bind
#print axioms eval_record
#print axioms eval_liftM
#print axioms eval_pure
#print axioms eval_if
#print axioms eval_flow
end NKE_Free
