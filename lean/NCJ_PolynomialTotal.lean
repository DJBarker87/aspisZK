import NCJ_HornerBytes
import NCJ_Constants
set_option autoImplicit false
noncomputable section
namespace NCJ_PolynomialTotal
open Aeneas Aeneas.Std Result AspisR1 LPi_FieldValues

def indices : List Usize := [6#usize,5#usize,4#usize,3#usize,2#usize,1#usize,0#usize]

def Domain (bytes : Slice U8) : Prop := bytes.val.length=224 ∧
  ∀ i : Usize,i.val<7 → ∀ part : Array U8 32#usize,
    part.val=(bytes.val.drop (32*i.val)).take 32 → NCJ_FieldTotal.Canonical part

theorem index_bound (i : Usize) (h : i∈indices) : i.val<7 := by
  simp only [indices,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide

/-- Complete source-port seven-step totality from canonical SAME224 bytes.
This does not install the distinct adopted polynomial carrier by renaming. -/
theorem source_port (bytes : Slice U8) (domain : Domain bytes) (x : NE) (hx : canonE x) :
    ∃ out,NCJ_HornerBytes.go bytes x indices FIo_Native.aspis_core.field.wide_exact.WideExact.ZERO=
      ok out ∧ canonE out := by
  apply NCJ_HornerBytes.source bytes x _ hx NCJ_Constants.zero indices
  intro i hi
  have bound:=index_bound i hi
  exact ⟨by rw [domain.1];omega,domain.2 i bound⟩

#print axioms index_bound
#print axioms source_port
end NCJ_PolynomialTotal
