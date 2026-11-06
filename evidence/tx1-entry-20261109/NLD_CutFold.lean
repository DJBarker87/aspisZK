import NLD_ParentState
set_option autoImplicit false
namespace AspisR1.NLD
open Aeneas Aeneas.Std Result
/-- Local NHZ-shaped fold: NHZ's concrete event carrier is digest-only. Entry
SDK/allocator occurrences need `Event`, which additionally carries both states.
This algebra supplies no native cut and no child packet by itself. -/
inductive Program (A : Type) where
 | done (value : A)
 | step {B : Type} (site : Site) (action : ParentState → Result B × ParentState)
     (next : B → ParentState → Program A)

/-- Abort returns its actual post-state, including effects before the abort;
no action is required to preserve the heap on failure. -/
def run {A : Type} : Program A → ParentState → Result A × ParentState × List Event
 | .done a, s => (.ok a,s,[])
 | .step site action k, s =>
   let (out,post) := action s
   match out with
   | .ok b =>
     let (result,final,tail) := run (k b post) post
     (result,final,⟨site,s,post⟩ :: tail)
   | .fail e => (.fail e,post,[⟨site,s,post⟩])
   | .div => (.div,post,[⟨site,s,post⟩])

/-- Explicit full-outcome cuts on one state chain. Every entered occurrence
carries its post-state, including failure and divergence prefixes. -/
inductive Cuts {A : Type} : Program A → ParentState → Result A → ParentState → List Event → Prop where
 | done (a : A) (s : ParentState) : Cuts (.done a) s (.ok a) s []
 | next {B : Type} (site : Site) (action : ParentState → Result B × ParentState)
     (k : B → ParentState → Program A) (pre post final : ParentState)
     (b : B) (result : Result A) (tail : List Event)
     (head : action pre = (.ok b,post))
     (rest : Cuts (k b post) post result final tail) :
     Cuts (.step site action k) pre result final (⟨site,pre,post⟩ :: tail)
 | fail {B : Type} (site : Site) (action : ParentState → Result B × ParentState)
     (k : B → ParentState → Program A) (pre post : ParentState) (e : Error)
     (head : action pre = (.fail e,post)) :
     Cuts (.step site action k) pre (.fail e) post [⟨site,pre,post⟩]
 | div {B : Type} (site : Site) (action : ParentState → Result B × ParentState)
     (k : B → ParentState → Program A) (pre post : ParentState)
     (head : action pre = (.div,post)) :
     Cuts (.step site action k) pre .div post [⟨site,pre,post⟩]

/-- Frames compose only where every individual occurrence proves the frame. -/
def Frames : List Event → Prop
 | [] => True
 | e :: es => Frame e.before e.after ∧ Frames es

/-- Every event's before state equals the preceding event's after state. -/
def Chain (initial final : ParentState) : List Event → Prop
 | [] => initial = final
 | e :: es => e.before = initial ∧ Chain e.after final es

theorem chain {A : Type} {p : Program A} {s t : ParentState}
    {r : Result A} {events : List Event} (cuts : Cuts p s r t events) :
    Chain s t events := by
  induction cuts with
  | done => rfl
  | next _ _ _ _ _ _ _ _ _ _ _ ih => exact ⟨rfl,ih⟩
  | fail => exact ⟨rfl,rfl⟩
  | div => exact ⟨rfl,rfl⟩

theorem frame_refl (s : ParentState) : Frame s s := ⟨rfl,rfl,rfl,rfl,rfl⟩

theorem frame_trans {a b c : ParentState} (ab : Frame a b) (bc : Frame b c) :
    Frame a c := ⟨ab.1.trans bc.1,ab.2.1.trans bc.2.1,
      ab.2.2.1.trans bc.2.2.1,ab.2.2.2.1.trans bc.2.2.2.1,
      ab.2.2.2.2.trans bc.2.2.2.2⟩

theorem frame_chain {s t : ParentState} {events : List Event}
    (chain : Chain s t events) (frames : Frames events) : Frame s t := by
  induction events generalizing s with
  | nil => cases chain; exact frame_refl _
  | cons e es ih =>
    rcases chain with ⟨eq,tail⟩
    subst s
    exact frame_trans frames.1 (ih tail frames.2)

#print axioms chain
#print axioms frame_refl
#print axioms frame_trans
#print axioms frame_chain
end AspisR1.NLD
