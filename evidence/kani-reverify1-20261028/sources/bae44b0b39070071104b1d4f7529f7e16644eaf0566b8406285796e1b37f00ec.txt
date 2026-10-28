import KMY_WindowTranslation
set_option autoImplicit false
namespace KMY_ViewComposition
open KMY_WindowComposition

theorem read_window32 {α : Type} (source before : Nat → α) (pos : Nat) :
    (fun j : Fin 32 => window source before pos 32 (pos+j.val)) =
      (fun j : Fin 32 => source j.val) := by
  funext j
  rw [window_spec, if_pos (by have h := j.isLt; omega)]
  congr 1
  omega

theorem decode_window32 {α β : Type} (decode : (Fin 32 → α) → β)
    (source before : Nat → α) (pos : Nat) :
    decode (fun j => window source before pos 32 (pos+j.val)) =
      decode (fun j => source j.val) := by
  rw [read_window32]

#print axioms read_window32
#print axioms decode_window32
end KMY_ViewComposition
