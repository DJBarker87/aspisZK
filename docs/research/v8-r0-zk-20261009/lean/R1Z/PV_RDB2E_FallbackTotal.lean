import R1Z.PV_RDB2E_FallbackArrayRead

section
-- Unchanged source component R1Z.PV_CBL_FallbackTotal
open Aeneas Aeneas.Std Result
namespace R1Z.PV_CBL_FallbackTotal
set_option autoImplicit false
def Total {A : Type} (r : Result A) : Prop := ∃ a, r=ok a
theorem pure {A : Type} (a : A) : Total (ok a) := ⟨a,rfl⟩
theorem bind {A B : Type} (x : Result A) (f : A→Result B)
    (hx : Total x) (hf : ∀ a, Total (f a)) : Total (x >>= f) := by
  obtain ⟨a,ha⟩ := hx
  obtain ⟨b,hb⟩ := hf a
  exact ⟨b,by simp only [ha,bind_tc_ok,hb]⟩
theorem read {T : Type} [Inhabited T] {N : Usize} (v : Array T N) (i : Usize)
    (h : i.val<N.val) : Total (Array.index_usize v i) :=
  ⟨_,PV_CBL_FallbackArrayRead.read v i h⟩
theorem update {T : Type} {N : Usize} (v : Array T N) (i : Usize) (t : T)
    (h : i.val<N.val) : Total (Array.update v i t) :=
  ⟨_,PV_CBL_ArrayStep.write v i t h⟩
#print axioms Total
#print axioms pure
#print axioms bind
#print axioms read
#print axioms update
end R1Z.PV_CBL_FallbackTotal

end
