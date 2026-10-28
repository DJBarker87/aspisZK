import Init
namespace PV_KStub_WindowFrame
/-- The length windows retain the original admitted domain. -/
theorem split_windows (P : Nat → Prop)
    (lo : ∀ n, n ≤ 129 → n ≤ 64 → P n)
    (hi : ∀ n, n ≤ 129 → 64 < n → P n) :
    ∀ n, n ≤ 129 → P n := by
  intro n hn
  cases Nat.lt_or_ge 64 n with
  | inl h => exact hi n hn h
  | inr h => exact lo n hn h
/-- Each window proves all coordinates; gluing preserves every coordinate. -/
theorem coordinate_frame {α : Type} (native reference : Nat → Nat → α)
    (lo : ∀ n, n ≤ 129 → n ≤ 64 → ∀ k, native n k = reference n k)
    (hi : ∀ n, n ≤ 129 → 64 < n → ∀ k, native n k = reference n k) :
    ∀ n, n ≤ 129 → ∀ k, native n k = reference n k :=
  split_windows (fun n => ∀ k, native n k = reference n k) lo hi
/-- Read-only views preserve coordinates outside any observed window. -/
theorem readonly_frame {α : Type} (before after : Nat → α)
    (readonly : after = before) (k : Nat) : after k = before k := by
  rw [readonly]
#print axioms split_windows
#print axioms coordinate_frame
#print axioms readonly_frame
end PV_KStub_WindowFrame
