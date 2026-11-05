import NIL_PortBind
set_option autoImplicit false
noncomputable section
namespace NIY_SectionBind
open Aeneas Aeneas.Std Result NIL_Carriers NIL_ResultTransport NIL_ResultReverse

/-- Lift a section callee reply into its exact try continuation, preserving every Err arm. -/
theorem sectionReply {A B C D : Type} (u : A → B) (f : C → D)
 (m : Result (core.result.Result A Cohort.Err))
 (left : B → Result (core.result.Result C Fresh.Err))
 (right : A → Result (core.result.Result D Cohort.Err))
 (h : ∀ x,outer (NIL_Carriers.inner f) (left (u x))=right x) :
 outer (NIL_Carriers.inner f)
 (do let reply ← outer (unInner u) m;NIL_TryTransport.fresh reply left)=
 (do let reply ← m;NIL_TryTransport.cohort reply right) := by
 apply NIL_PortBind.source
 intro reply
 rw [NIL_TryTransport.map_try]
 cases reply with
 | Ok x => exact h x
 | Err err => rfl

/-- Invert a checked forward port using its actual carrier retraction. -/
theorem reverse_port {A B : Type} (f : A → B) (g : B → A)
 (law : ∀ x,g (f x)=x) (m : Result A) (n : Result B) (h : outer f m=n) :
 m=outer g n := by
 rw [←h]
 exact (outer_roundtrip f g law m).symm

/-- Consume a forward callee port, with a checked carrier retraction, at its exact try call. -/
theorem forwardReply {A B C D : Type} (f : A → B) (g : B → A) (out : C → D)
 (law : ∀ x,g (f x)=x)
 (m : Result (core.result.Result A Fresh.Err))
 (n : Result (core.result.Result B Cohort.Err))
 (port : outer (NIL_Carriers.inner f) m=n)
 (left : A → Result (core.result.Result C Fresh.Err))
 (right : B → Result (core.result.Result D Cohort.Err))
 (next : ∀ x,outer (NIL_Carriers.inner out) (left (g x))=right x) :
 outer (NIL_Carriers.inner out) (do let reply ← m;NIL_TryTransport.fresh reply left)=
 (do let reply ← n;NIL_TryTransport.cohort reply right) := by
 rw [reverse_port (NIL_Carriers.inner f) (unInner g)
   (inner_roundtrip f g law) m n port]
 exact sectionReply g out n left right next
#print axioms forwardReply
#print axioms sectionReply
#print axioms reverse_port
end NIY_SectionBind
