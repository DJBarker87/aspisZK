import LIBC_PreparedPrefix
set_option autoImplicit false
noncomputable section
namespace LIBC_PreparedLaw
open Aeneas Aeneas.Std Result AspisR1 AspisR1PublicPreparation
open NFW_PreparedControl
abbrev Args := r1_semantic.Verified Unit × verifier.View × Scratch
abbrev Output := Except LIB_VCarriers.VErr LIB_VCarriers.Prepared × LIB_VCarriers.E29
def error : verifier.Error → LIB_VCarriers.VErr
 | .Parse => .Parse | .Semantic => .Semantic | .Transcript => .Transcript
 | .Relation => .Relation | .Merkle => .Merkle | .Query => .Query
 | .Checkpoint => .Checkpoint | .Allocation => .Allocation
def port (r : Out) : Output :=
 ((match r.1 with | .Ok p => .ok p | .Err e => .error (error e)),r.2)
def run (a : Args) (env : RSL.Env) :=
 PreparedHashCode.run (LIBC_PreparedLog.code (LIBC_PreparedLog.digest env) a.1 a.2.1 () a.2.2)
def prefixRun (a : Args) (env : RSL.Env) :=
 PreparedHashCode.run (LIBC_PreparedPrefix.preludeCode (LIBC_PreparedLog.digest env) a.1 a.2.1)
def FoldReached (r : Result LIBC_PreparedPrefix.Prelude) : Prop :=
 match r with | .ok (_,_,_,_,n) => n = 2#usize | _ => False
def BoxReached (r : Result Out) : Prop :=
 match r with | .ok (.Ok _,_) => True | _ => False
/-- Only the returned value evaluator uses a fallback on a stopped model.
No returned value or post-abort scratch is asserted on those arms. -/
def value (a : Args) (env : RSL.Env) : Output :=
 match (run a env).2 with | .ok r => port r | _ => (.error .Parse,a.2.2)
/-- Deterministic CLOSED model graph plus exactly the two named infallible
allocation prefixes: fold Vec and final successful Box. Fold reach is computed
from the SAME source prelude, including all rejected/stopped prefixes. -/
def law (a : Args) : RSL.Spec Output := fun env o =>
 o = LIB_Carriers.resultObs port (LIBC_PreparedLog.events (run a env).1) (run a env).2 ∨
 (FoldReached (prefixRun a env).2 ∧
  o = ⟨.abort,LIBC_PreparedLog.events (prefixRun a env).1⟩) ∨
 (BoxReached (run a env).2 ∧ o = ⟨.abort,LIBC_PreparedLog.events (run a env).1⟩)
/-- Every returned arm, including both Rust Errors, is precisely the full
model graph at the SAME sem/View/g and with the SAME ordered log. -/
theorem returned (a : Args) (env : RSL.Env) (r : Output) (ev : List RSL.Event) :
 law a env ⟨.ret r,ev⟩ ↔ ∃ native,
 (run a env).2 = .ok native ∧ r = port native ∧ ev = LIBC_PreparedLog.events (run a env).1 := by
 cases h : (run a env).2 <;> simp [law,h,LIB_Carriers.resultObs]
theorem returns (a : Args) (env : RSL.Env) :
 NND_Returned.Returns (law a) env (value a env) := by
 intro o r ho hr
 rcases o with ⟨exit,ev⟩
 dsimp only at hr
 subst exit
 obtain ⟨native,hn,reply,_⟩ := (returned a env r ev).mp ho
 rw [reply,value,hn]
def Failed (r : Result Out) : Prop := match r with | .fail _ => True | _ => False
/-- No other allocation prefix and no post-abort value appears in the law. -/
theorem abort_exact (a : Args) (env : RSL.Env) (ev : List RSL.Event) :
 law a env ⟨.abort,ev⟩ ↔
 (Failed (run a env).2 ∧ ev = LIBC_PreparedLog.events (run a env).1) ∨
 (FoldReached (prefixRun a env).2 ∧ ev = LIBC_PreparedLog.events (prefixRun a env).1) ∨
 (BoxReached (run a env).2 ∧ ev = LIBC_PreparedLog.events (run a env).1) := by
 cases h : (run a env).2 <;> simp [law,h,Failed,LIB_Carriers.resultObs]
theorem divergence_exact (a : Args) (env : RSL.Env) (ev : List RSL.Event) :
 law a env ⟨.diverge,ev⟩ ↔
 (run a env).2 = .div ∧ ev = LIBC_PreparedLog.events (run a env).1 := by
 cases h : (run a env).2 <;> simp [law,h,LIB_Carriers.resultObs]
theorem native_result (a : Args) (env : RSL.Env) :
 (run a env).2 = NGN_Emitted.prepared NHL_PreparedScalars.actual
 (LIBC_PreparedLog.digest env) a.1 a.2.1 () a.2.2 :=
 LIBC_PreparedLog.source_at_env env a.1 a.2.1 a.2.2
theorem capacity : (32#usize + 224#usize : Result Usize) = .ok 256#usize := rfl
#print axioms returned
#print axioms returns
#print axioms abort_exact
#print axioms divergence_exact
#print axioms native_result
#print axioms capacity
end LIBC_PreparedLaw
