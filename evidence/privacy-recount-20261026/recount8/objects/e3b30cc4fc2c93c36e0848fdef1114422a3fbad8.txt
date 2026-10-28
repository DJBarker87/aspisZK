import R1Z.PV_W_Syntax
set_option autoImplicit false
namespace R1Z.PV_RunJoin_RunProjection39
open PV_W_Threading PV_W_Syntax
universe u
variable {W V C D E A B : Type} {Op : Type → Type u}

/-- Project a full effect receipt. Failures and divergence keep the post-world
and every call; no Result-only erasure is used. -/
def receipt (world : W → V) (event : W → C → D) (r : Run W C E A) : Run V D E A :=
  ⟨r.outcome,world r.world,r.calls.map (fun c => (world c.1,event c.1 c.2))⟩

theorem bind (world : W → V) (event : W → C → D)
    (m : M W C E A) (n : M V D E A)
    (k : A → M W C E B) (l : A → M V D E B)
    (hm : ∀ w, receipt world event (m w) = n (world w))
    (hk : ∀ a w, receipt world event (k a w) = l a (world w)) (w : W) :
    receipt world event (PV_W_Threading.bind m k w) =
      PV_W_Threading.bind n l (world w) := by
  unfold PV_W_Threading.bind
  rw [← hm w]
  cases h : (m w).outcome with
  | fail e => simp only [PV_W_Threading.bind,receipt,h]
  | div => simp only [PV_W_Threading.bind,receipt,h]
  | ok a =>
    simp only [PV_W_Threading.bind,receipt,h]
    rw [← hk a (m w).world]
    simp only [receipt,List.map_append]

/-- Syntax-directed receipt projection, including the complete failed prefix.
Its operation law remains a per-helper source/native obligation. -/
theorem eval (world : W → V) (event : W → C → D)
    (left : Interpreter Op W C E) (right : Interpreter Op V D E)
    (law : ∀ {T} (op : Op T) w, receipt world event (left op w) = right op (world w))
    (p : Program Op E A) (w : W) :
    receipt world event (PV_W_Syntax.eval left p w) =
      PV_W_Syntax.eval right p (world w) := by
  induction p generalizing w with
  | pure a => rfl
  | failure e => rfl
  | diverge => rfl
  | call op next ih => exact bind world event (left op) (right op) _ _ (law op) ih w

#print axioms bind
#print axioms eval
end R1Z.PV_RunJoin_RunProjection39
