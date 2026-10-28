import Std
set_option autoImplicit false
namespace KMX_CopyMeaning
/-- Value-level semantics for explicit indexed writes. Pointer validity,
non-overlap, lengths and allocation remain caller obligations. -/
def write {α : Type} (dst : Nat → α) (i : Nat) (v : α) : Nat → α :=
  fun k => if k = i then v else dst k

def loop {α : Type} (src dst : Nat → α) (start : Nat) : Nat → Nat → α
  | 0 => dst
  | n+1 => loop src (write dst start (src start)) (start+1) n

theorem loop_spec {α : Type} (src dst : Nat → α) (start count k : Nat) :
    loop src dst start count k =
      if start ≤ k ∧ k < start + count then src k else dst k := by
  induction count generalizing dst start with
  | zero => simp [loop]
  | succ n ih =>
    rw [loop, ih]
    simp only [write]
    split <;> split <;> split <;> simp_all <;> omega

theorem copy_prefix {α : Type} (src dst : Nat → α) (count k : Nat) :
    loop src dst 0 count k = if k < count then src k else dst k := by
  simpa using loop_spec src dst 0 count k

theorem copy_frame {α : Type} (src dst : Nat → α) (start count k : Nat)
    (outside : k < start ∨ start + count ≤ k) :
    loop src dst start count k = dst k := by
  rw [loop_spec, if_neg]; omega

/-- Vector append value law. This says nothing about allocation failure,
capacity, pointer identity, or the allocator's reallocation implementation. -/
def appendLoop {α : Type} (dst : List α) : List α → List α
  | [] => dst
  | x::xs => appendLoop (dst ++ [x]) xs

theorem append_spec {α : Type} (dst src : List α) :
    appendLoop dst src = dst ++ src := by
  induction src generalizing dst with
  | nil => simp [appendLoop]
  | cons x xs ih => simp [appendLoop, ih, List.append_assoc]

#print axioms loop_spec
#print axioms copy_prefix
#print axioms copy_frame
#print axioms append_spec
end KMX_CopyMeaning
