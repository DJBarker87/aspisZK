import S2E_Model

set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1.S2J

/-- Rust core array/equality.rs PartialEq<[U; N]> for [T] delegates to
slice equality. This is the existing TrustedStd boundary, not a caller law. -/
def sliceArrayEq {T U : Type} {N : Usize} (cmp : core.cmp.PartialEq T U)
    (s : Slice T) (a : Array U N) : Result Bool :=
  core.slice.cmp.PartialEqSlice.eq cmp s a.to_slice

def installEquality (ops : S2E_Reference.Ops) : S2E_Reference.Ops :=
  {ops with op1 := sliceArrayEq}

/-- Concrete installed port, preserving every other operation. -/
theorem op1_port (ops : S2E_Reference.Ops) {T U : Type} {N : Usize}
    (cmp : core.cmp.PartialEq T U) (s : Slice T) (a : Array U N) :
    (installEquality ops).op1 cmp s a =
      core.slice.cmp.PartialEqSlice.eq cmp s a.to_slice := rfl

theorem byte_equality (s t : Slice U8) :
    core.slice.cmp.PartialEqSlice.eq core.cmp.PartialEqU8 s t =
      ok (decide (s = t)) := by
  have spec := core.slice.cmp.PartialEqSlice.eq_homo_spec core.cmp.PartialEqU8 s t
    (by intro x y; simp [core.cmp.PartialEqU8, WP.spec_ok])
  obtain ⟨b, hb, equal⟩ := WP.spec_imp_exists spec
  rw [hb]
  congr 1
  cases b <;> simp_all

#print axioms op1_port
#print axioms byte_equality
end AspisR1.S2J
