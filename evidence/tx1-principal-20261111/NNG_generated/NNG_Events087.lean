import NNG_PreparedCall087
import NNG_Events137
import NNG_TypedEvents
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_Events087
open Aeneas Aeneas.Std NMP_prepare
abbrev ObservedArgs := NMP_Emitted.Public × Slice U8 × Unit × NMP_Emitted.Observer
abbrev PreparedArgs := r1_semantic.Verified Unit × verifier.View × Unit × NMP_Emitted.Scratch

def observed (env : RSL.Env) (a : ObservedArgs) : List RSL.Event :=
 (NMT_CallTree.run (NNG_Tree137.tree (NNG_Context137.calls env)
   ⟨NNG_PublicSource137.digest env,a.1,a.2.1,(),a.2.2.2⟩)).2.flatMap (NNG_Events137.events env)
def prepared (env : RSL.Env) (a : PreparedArgs) : List RSL.Event :=
 LIBC_PreparedLog.events (AspisR1PublicPreparation.PreparedHashCode.run
   (NNG_PreparedCall087.code (NNG_PublicSource137.digest env) a.1 a.2.1 () a.2.2.2)).1

def events (env : RSL.Env) (event : NMT_CallTree.Event) : List RSL.Event :=
 NNG_TypedEvents.select "TX1:137/verify_observed" (observed env) event ++
 NNG_TypedEvents.select "TX1:179/Prepared_new" (prepared env) event

theorem observed_call {Reply : Type} (env : RSL.Env) (a : ObservedArgs) (reply : Result Reply) :
 events env (.call "TX1:137/verify_observed" a reply)=observed env a := by
 simp [events,NNG_TypedEvents.select]
theorem prepared_call {Reply : Type} (env : RSL.Env) (a : PreparedArgs) (reply : Result Reply) :
 events env (.call "TX1:179/Prepared_new" a reply)=prepared env a := by
 simp [events,NNG_TypedEvents.select]
theorem silent {Args Reply : Type} (env : RSL.Env) (site : String) (a : Args) (reply : Result Reply)
 (h0 : site≠"TX1:137/verify_observed") (h1 : site≠"TX1:179/Prepared_new") :
 events env (.call site a reply)=[] := by simp [events,NNG_TypedEvents.select,h0,h1]
#print axioms observed_call
#print axioms prepared_call
#print axioms silent
end AspisR1.NNG_Events087
