import Aeneas
set_option autoImplicit false
namespace PV_B2_ArrayTotal
open Aeneas Aeneas.Std Result

def Total {α : Type} (r : Result α) : Prop := ∃ x, r = ok x

theorem bind {α β : Type} (r : Result α) (k : α → Result β)
    (hr : Total r) (hk : ∀ x, Total (k x)) : Total (r >>= k) := by
  obtain ⟨x,hx⟩ := hr
  obtain ⟨y,hy⟩ := hk x
  exact ⟨y,by simp only [hx,bind_tc_ok,hy]⟩

theorem read {α : Type} {n : Usize} (xs : Array α n) (i : Usize)
    (h : i.val < n.val) : Total (Array.index_usize xs i) := by
  obtain ⟨x,hx,_⟩ := WP.spec_imp_exists
    (Array.index_usize_spec xs i (by
      change i.val < xs.val.length
      simpa only [xs.property] using h))
  exact ⟨x,hx⟩

theorem write {α : Type} {n : Usize} (xs : Array α n) (i : Usize) (x : α)
    (h : i.val < n.val) : Total (Array.update xs i x) := by
  obtain ⟨ys,hy,_⟩ := WP.spec_imp_exists
    (Array.update_spec xs i x (by
      change i.val < xs.val.length
      simpa only [xs.property] using h))
  exact ⟨ys,hy⟩

theorem borrow {α : Type} {n : Usize} (xs : Array α n) (i : Usize)
    (h : i.val < n.val) : Total (Array.index_mut_usize xs i) := by
  obtain ⟨x,hx⟩ := read xs i h
  exact ⟨(x,xs.set i),by simp only [Array.index_mut_usize,hx,bind_tc_ok]⟩

def RustOk {α ε : Type} (r : Result (core.result.Result α ε)) : Prop :=
  ∃ x, r = ok (.Ok x)

theorem bind_rust {α β ε : Type} (r : Result α)
    (k : α → Result (core.result.Result β ε))
    (hr : Total r) (hk : ∀ x, RustOk (k x)) : RustOk (r >>= k) := by
  obtain ⟨x,hx⟩ := hr
  obtain ⟨y,hy⟩ := hk x
  exact ⟨y,by simp only [hx,bind_tc_ok,hy]⟩
#print axioms bind
#print axioms read
#print axioms write
#print axioms borrow
#print axioms bind_rust
end PV_B2_ArrayTotal
