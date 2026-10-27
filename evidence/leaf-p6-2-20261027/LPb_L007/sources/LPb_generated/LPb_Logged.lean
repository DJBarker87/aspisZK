import LPb_CheckpointLayout
open Aeneas Aeneas.Std Result
namespace LPb_Logged
abbrev Query := List (Slice U8)
abbrev Run (α : Type) := List Query × Result α
def lift {α : Type} (r : Result α) : Run α := ([],r)
def bind {α β : Type} (r : Run α) (k : α → Run β) : Run β :=
  match r.2 with
  | ok a => let s := k a; (r.1 ++ s.1,s.2)
  | fail e => (r.1,fail e)
  | div => (r.1,div)
def attempt {H : Type} (D : XRk_Release.aspis_core.digest.Digest32 H) (hash : H)
    (q : Query) : Run (Array U8 32#usize) := ([q],XRk_digest D hash q)
theorem erase_bind {α β : Type} (r : Run α) (k : α → Run β) :
    (bind r k).2 = (do let a ← r.2; (k a).2) := by
  rcases r with ⟨tr,r⟩
  cases r <;> rfl

theorem bind_ok {α β : Type} (tr : List Query) (a : α) (k : α → Run β) :
    bind (tr,ok a) k = (tr ++ (k a).1,(k a).2) := rfl

theorem bind_failure {α β : Type} (tr : List Query) (e : Error) (k : α → Run β) :
    bind (tr,fail e) k = (tr,fail e) := rfl

theorem bind_diverge {α β : Type} (tr : List Query) (k : α → Run β) :
    bind (tr,div) k = (tr,div) := rfl

theorem attempted_failure {H : Type} (D : XRk_Release.aspis_core.digest.Digest32 H)
    (hash : H) (q : Query) (e : Error) (run : XRk_digest D hash q = fail e) :
    attempt D hash q = ([q],fail e) := by
  unfold attempt
  rw [run]
#print axioms erase_bind
#print axioms bind_ok
#print axioms bind_failure
#print axioms bind_diverge
#print axioms attempted_failure
end LPb_Logged
