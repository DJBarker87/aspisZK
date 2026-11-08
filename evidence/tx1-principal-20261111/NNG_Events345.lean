import NNG_TreeTail345
import NNG_TypedEvents
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_Events345
open Aeneas Aeneas.Std Result NMT_345 NMT_CallTree NNG_TreeTail345

def child (env : RSL.Env) (a : ChildArgs) : List RSL.Event :=
 NNG_ChildSource345.events env a.1 a.2.1 a.2.2.1 a.2.2.2

def events (env : RSL.Env) : NMT_CallTree.Event → List RSL.Event :=
 NNG_TypedEvents.select "TX1:328/first_decoded" (child env)

theorem child_call {Reply : Type} (env : RSL.Env) (a : ChildArgs) (r : Result Reply) :
 events env (.call "TX1:328/first_decoded" a r)=child env a := by
 simp [events,NNG_TypedEvents.select]
#print axioms child_call

theorem observation (env : RSL.Env) (pub : Public) (publicBytes proof : Slice U8) (k : Usize)
 (bound : k.val≤UScalar.cMax .Usize) :
 NNG_Observed136.observation NNG_ChildSource345.port (events env)
  (invoke "TX1:328/first_decoded" (pub,publicBytes,proof,k) (NNG_ChildSource345.call env pub publicBytes proof k))=
 NNG_Producer328.producer (NNG_ChildSource345.args pub publicBytes proof k) env := by
 rw [NNG_InvokeGraph328.observation,child_call]
 exact NNG_ChildSource345.observation env pub publicBytes proof k bound
#print axioms observation
end AspisR1.NNG_Events345
