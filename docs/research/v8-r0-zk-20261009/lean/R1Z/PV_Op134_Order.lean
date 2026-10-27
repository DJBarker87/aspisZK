import R1Z.PV_CBM_InventoryShape
import Mathlib.Data.List.Pairwise
namespace R1Z.PV_Op134_Order
set_option autoImplicit false
abbrev Cell := ProverRwFull.aspis_statement.trace_v4.TraceCell
def key (c : Cell) : Nat := 1024 * c.column.val + c.row.val
def increasing (xs : List Cell) : Prop := xs.Pairwise (fun a b => key a < key b)

theorem append {xs ys : List Cell} (hx : increasing xs) (hy : increasing ys)
    (hcross : ∀ a ∈ xs, ∀ b ∈ ys, key a < key b) : increasing (xs ++ ys) := by
  exact List.pairwise_append.mpr ⟨hx,hy,hcross⟩

theorem nodup {xs : List Cell} (h : increasing xs) : xs.Nodup := by
  change List.Pairwise (fun a b : Cell => a ≠ b) xs
  exact h.imp (by intro a b hlt heq; subst b; exact (Nat.lt_irrefl _) hlt)

theorem key_injective {a b : Cell} (ha : a.row.val < 1024)
    (hb : b.row.val < 1024) (h : key a = key b) : a = b := by
  have hr : a.row.val = b.row.val := by unfold key at h; omega
  have hc : a.column.val = b.column.val := by unfold key at h; omega
  cases a; cases b
  congr 1 <;> apply Aeneas.Std.UScalar.eq_of_val_eq <;> assumption
theorem append_bounds {xs ys : List Cell} {lo mid hi : Nat}
    (hx : increasing xs ∧ ∀ c ∈ xs, lo ≤ key c ∧ key c < mid ∧ c.row.val < 1024 ∧ c.column.val < 16)
    (hlo : lo ≤ mid) (hhi : mid ≤ hi)
    (hy : increasing ys ∧ ∀ c ∈ ys, mid ≤ key c ∧ key c < hi ∧ c.row.val < 1024 ∧ c.column.val < 16) :
    increasing (xs ++ ys) ∧ ∀ c ∈ xs ++ ys, lo ≤ key c ∧ key c < hi ∧ c.row.val < 1024 ∧ c.column.val < 16 := by
  constructor
  · exact append hx.1 hy.1 (by intro a ha b hb; have := hx.2 a ha; have := hy.2 b hb; omega)
  · intro c hc
    rcases List.mem_append.mp hc with hc | hc
    · have h := hx.2 c hc

      omega
    · have h := hy.2 c hc
      omega
#print axioms append
#print axioms append_bounds
#print axioms nodup
#print axioms key_injective
end R1Z.PV_Op134_Order
