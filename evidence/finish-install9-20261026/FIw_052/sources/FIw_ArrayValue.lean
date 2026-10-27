import FIv_NativeArray
set_option autoImplicit false
noncomputable section
namespace AspisR1.FIw_ArrayValue
open Aeneas Aeneas.Std Result WP
open FIv_NativeArithmetic (NQ)
open FIv_NativeValue (K Canon decode)
def cells {N : Usize} (a : Array NQ N) (i : Fin N.val) : NQ :=
  a.val[i.val]'(by simpa only [a.property] using i.isLt)
def decoded {N : Usize} (a : Array NQ N) (i : Fin N.val) : K := decode (cells a i)
def canonical {N : Usize} (a : Array NQ N) : Prop := ∀ x∈a.val,Canon x

theorem update {N : Usize} (a b : Array NQ N) (i : Usize) (x : NQ)
    (hi : i.val<N.val) (ha : canonical a) (hx : Canon x)
    (run : Array.update a i x=ok b) :
    canonical b ∧ decoded b=Function.update (decoded a) ⟨i.val,hi⟩ (decode x) := by
  unfold Array.update at run
  split at run
  · cases run
  · have same := Result.ok.inj run
    subst b
    constructor
    · intro y hy
      exact (List.mem_set.mp hy).elim (fun eq=>eq ▸ hx) (fun old=>ha y old)
    · funext j
      change decode ((a.val.set i.val x)[j.val]'_) = _
      by_cases he : i.val=j.val
      · have e : j=(⟨i.val,hi⟩ : Fin N.val) := Fin.ext he.symm
        subst j
        rw [List.getElem_set_self]
        simp only [Function.update_self]
      · rw [List.getElem_set_ne he]
        have e : j≠(⟨i.val,hi⟩ : Fin N.val) := fun h=>he (congrArg Fin.val h).symm
        rw [Function.update_of_ne e]
        rfl
#print axioms update
end AspisR1.FIw_ArrayValue
end
