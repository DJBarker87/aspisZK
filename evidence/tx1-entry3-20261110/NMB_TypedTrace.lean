import NLD_SourceTrace
set_option autoImplicit false
namespace NMB_TypedTrace
open Aeneas Aeneas.Std Result AspisR1
/-- Explicit heterogeneous source values, not callbacks or address witnesses. -/
structure Packed where
 type : Type
 value : type
def pack {A : Type} (value : A) : Packed := ⟨A,value⟩
abbrev Environment := List (String × Packed)
/-- Every source occurrence records its complete nominal Result and the live
source argument/local values. Physical allocator/syscall effects are separate
child-packet obligations; this is not an installed native interpretation. -/
structure Event where
 site : Nat
 environment : Environment
 type : Type
 reply : Result type
structure Run (A : Type) where
 events : List Event
 result : Result A
def pure {A : Type} (value : A) : Run A := ⟨[],.ok value⟩
def bind {A B : Type} (m : Run A) (f : A → Run B) : Run B :=
 match m.result with
 | .fail e=>⟨m.events,.fail e⟩
 | .div=>⟨m.events,.div⟩
 | .ok value=>let tail:=f value;⟨m.events++tail.events,tail.result⟩
instance : Monad Run where
 pure:=NMB_TypedTrace.pure
 bind:=NMB_TypedTrace.bind
def call {A : Type} (site : Nat) (environment : Environment) (reply : Result A) : Run A :=
 ⟨[⟨site,environment,A,reply⟩],reply⟩
def forget {A : Type} (m : Run A) : NLD_SourceTrace.Trace A :=
 (m.events.map Event.site,m.result)
theorem forget_call {A : Type} (site : Nat) (env : Environment) (reply : Result A) :
 forget (call site env reply)=NLD_SourceTrace.call site reply := rfl
theorem forget_pure {A : Type} (a : A) : forget (pure a)=NJD_Trace.pure a := rfl
theorem forget_bind {A B : Type} (m : Run A) (f : A → Run B) :
 forget (m >>= f)=NJD_Trace.bind (forget m) (fun a=>forget (f a)) := by
 cases m with
 | mk events result=>
  cases result <;> simp [Bind.bind,bind,forget,NJD_Trace.bind,List.map_append]
theorem forget_if {A : Type} (p : Prop) [Decidable p] (yes no : Run A) :
 forget (if p then yes else no)=if p then forget yes else forget no := by split <;> rfl
theorem legacy_bind_congr {A B : Type} (m : NLD_SourceTrace.Trace A)
 (f g : A → NLD_SourceTrace.Trace B) (same : ∀ a, f a=g a) :
 NJD_Trace.bind m f=NJD_Trace.bind m g :=
 congrArg (fun k=>NJD_Trace.bind m k) (funext same)
theorem fail_prefix {A B : Type} (m : Run A) (f : A → Run B) (e : Aeneas.Std.Error)
 (failed : m.result=.fail e) : (m >>= f).events=m.events := by simp [Bind.bind,bind,failed]
theorem div_prefix {A B : Type} (m : Run A) (f : A → Run B)
 (diverged : m.result=.div) : (m >>= f).events=m.events := by simp [Bind.bind,bind,diverged]
#print Event
#print Run
#print axioms forget_call
#print axioms forget_pure
#print axioms forget_bind
#print axioms forget_if
#print axioms legacy_bind_congr
#print axioms fail_prefix
#print axioms div_prefix
end NMB_TypedTrace
