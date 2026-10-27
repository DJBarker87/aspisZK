import R1Z.PV_CBM_PushList
namespace R1Z.PV_CBM_ListComposition
open Aeneas Aeneas.Std Result
set_option autoImplicit false

theorem append_free {α : Type} {p : α → Prop} {xs ys : List α}
    (hx : ∀ x ∈ xs, p x) (hy : ∀ x ∈ ys, p x) :
    ∀ x ∈ xs ++ ys, p x := by
  intro x h
  rcases List.mem_append.mp h with h | h
  · exact hx x h
  · exact hy x h

theorem length_step {α : Type} {out next : alloc.vec.Vec α}
    {xs : List α} {n base offset : Nat}
    (hv : next.val = out.val ++ xs) (hx : xs.length = n)
    (hp : out.val.length = base + offset) :
    next.val.length = base + (offset + n) := by
  rw [hv,List.length_append,hx,hp,Nat.add_assoc]

theorem capacity_step {α : Type} {out : alloc.vec.Vec α}
    {base offset size : Nat} (hc : base + 3803 ≤ 4096)
    (hl : out.val.length = base + offset) (hs : offset + size ≤ 3803) :
    out.val.length + size ≤ 4096 := by omega

#print axioms append_free
#print axioms length_step
#print axioms capacity_step
end R1Z.PV_CBM_ListComposition
