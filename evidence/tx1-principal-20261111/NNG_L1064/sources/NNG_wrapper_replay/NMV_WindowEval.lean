import NMV_RslFold
set_option autoImplicit false
namespace NMV_WindowEval
open RSL

/-- Evaluate a returning/stopped window without inventing a post-abort world. -/
def bind {A B : Type} (o : Obs A) (k : A → Obs B) : Obs B :=
 match o.exit with
 | .ret a => let p := k a; ⟨p.exit, o.events ++ p.events⟩
 | .abort => ⟨.abort,o.events⟩
 | .diverge => ⟨.diverge,o.events⟩

def pure {A : Type} (a : A) : Obs A := ⟨.ret a,[]⟩

theorem bind_mem {A B : Type} (m : Spec A) (k : A → Spec B)
 (o : Obs A) (f : A → Obs B) (env : Env)
 (hm : m env o) (hk : ∀ a, k a env (f a)) :
 Spec.bind m k env (bind o f) := by
 rcases o with ⟨exit,es⟩
 cases exit with
 | ret a => exact Or.inl ⟨a,es,f a,hm,hk a,rfl⟩
 | abort => exact Or.inr (Or.inl ⟨es,hm,rfl⟩)
 | diverge => exact Or.inr (Or.inr ⟨es,hm,rfl⟩)

/-- Only individual SDK/std/runtime laws, never a wrapper-result premise.
The snapshot law includes allocation aborts, failed acquisition and guard
release; copy includes exclusive failure, length panic, write and release. -/
structure Windows where
 snapshot : AccountInfo → Nat → Nat → SdkState → Env → Obs (OwnedAccount × SdkState)
 clear : Bytes → Env → Obs Unit
 clock : Env → Obs (Except ProgramError UInt64)
 copy : AccountInfo → Bytes → SdkState → Env → Obs (Except ProgramError Unit × SdkState)
 snapshot_law : ∀ a l1 l2 s env, RSL.snapshot a l1 l2 s env (snapshot a l1 l2 s env)
 clear_law : ∀ b env, Spec.emit (.returnData b) env (clear b env)
 clock_law : ∀ env,
   (Spec.bind (Spec.env Env.clock) fun c =>
      Spec.bind (Spec.emit (.clock c)) fun _ => Spec.pure c) env (clock env)
 copy_law : ∀ a b s env, TX1_344.copyStep a b s env (copy a b s env)

/-- Source array evaluation order; descriptors and complete owned replies. -/
def snapshots (w : Windows) : List AccountInfo → List (Nat × Nat) → SdkState → Env → Obs (List OwnedAccount × SdkState)
 | a::as,(x,y)::ls,s,env =>
   bind (w.snapshot a x y s env) fun r =>
   bind (snapshots w as ls r.2 env) fun t => pure (r.1::t.1,t.2)
 | _,_,s,_ => pure ([],s)

theorem snapshots_law (w : Windows) (as : List AccountInfo) (ls : List (Nat × Nat))
 (s : SdkState) (env : Env) :
 TX2_240.snapAll as ls s env (snapshots w as ls s env) := by
 induction as generalizing ls s with
 | nil => rfl
 | cons a as ih =>
   cases ls with
   | nil => rfl
   | cons l ls =>
     rcases l with ⟨x,y⟩
     apply bind_mem _ _ _ _ env (w.snapshot_law a x y s env)
     intro r
     apply bind_mem _ _ _ _ env (ih ls r.2)
     intro t
     rfl

#print axioms bind_mem
#print axioms snapshots_law
end NMV_WindowEval
