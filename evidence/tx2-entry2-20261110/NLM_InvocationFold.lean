import NLM_PacketTypes
set_option autoImplicit false
namespace NLM_InvocationFold
open Aeneas Aeneas.Std NLM_PacketTypes
/-- Stateful chronological interpretation: the returned native post-frame is
always the next cut's input. fail/div retain the post at the abort prefix. -/
abbrev Program (Ambient Event Reply : Type) := World Ambient → Observation Ambient Event Reply

def pure {Ambient Event A : Type} (a : A) : Program Ambient Event A :=
 fun world => ⟨world,⟨.ok a,[]⟩⟩
def bind {Ambient Event A B : Type} (head : Program Ambient Event A)
 (tail : A → Program Ambient Event B) : Program Ambient Event B := fun world =>
 let h := head world
 match h.run.result with
 | .fail err => ⟨h.post,⟨.fail err,h.run.events⟩⟩
 | .div => ⟨h.post,⟨.div,h.run.events⟩⟩
 | .ok value =>
   let t := tail value h.post
   ⟨t.post,⟨t.run.result,h.run.events++t.run.events⟩⟩
/-- A same-world equality at each source occurrence is sufficient. No inverse
association to an independently selected transcript is required. -/
theorem bind_equal {Ambient Event A B : Type}
 (head head' : Program Ambient Event A) (tail tail' : A → Program Ambient Event B)
 (h : ∀ world,head world=head' world)
 (t : ∀ a world,tail a world=tail' a world) (world : World Ambient) :
 bind head tail world=bind head' tail' world := by
 unfold bind
 rw [h]
 dsimp only
 cases hr : (head' world).run.result with
 | fail err => simp only [hr]
 | div => simp only [hr]
 | ok a => simp only [hr]; rw [t]
theorem abort_prefix {Ambient Event A B : Type}
 (head : Program Ambient Event A) (tail : A → Program Ambient Event B)
 (world : World Ambient) (err : Aeneas.Std.Error)
 (aborted : (head world).run.result=.fail err) :
 bind head tail world=⟨(head world).post,⟨.fail err,(head world).run.events⟩⟩ := by
 simp only [bind,aborted]
theorem diverge_prefix {Ambient Event A B : Type}
 (head : Program Ambient Event A) (tail : A → Program Ambient Event B)
 (world : World Ambient) (aborted : (head world).run.result=.div) :
 bind head tail world=⟨(head world).post,⟨.div,(head world).run.events⟩⟩ := by
 simp only [bind,aborted]
#print bind_equal
#print abort_prefix
#print diverge_prefix
#print axioms bind_equal
#print axioms abort_prefix
#print axioms diverge_prefix
end NLM_InvocationFold
