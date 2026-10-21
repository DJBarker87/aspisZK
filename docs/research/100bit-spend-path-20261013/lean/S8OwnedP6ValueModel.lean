import S8OwnedP6.Funs
import S7OwnedP6ScalarProof
import Mathlib.Tactic.FinCases

/-! Concrete emitted residue/reducer semantics. No arithmetic external remains. -/
set_option autoImplicit false
namespace S8OwnedP6ValueModel
open Aeneas Aeneas.Std Result
open S8OwnedP6
abbrev Q := aspis_core.field.QM31
abbrev Row := Array U64 4#usize

def rowAt (row : Row) (j : Fin 4) : U64 :=
  row.val[j.val]'(by simpa [row.property] using j.isLt)
def coordinate (q : Q) (j : Fin 4) : U32 :=
  match j.val with | 0 => q.c0.a | 1 => q.c0.b | 2 => q.c1.a | _ => q.c1.b

theorem reducer_eq (x : U64) :
    aspis_core.field.M31.reduce_u64 x =
      AspisR1Qm31ArithmeticProbe.field.M31.reduce_u64 x := by
  unfold aspis_core.field.M31.reduce_u64 aspis_core.field.reduce_u64
    AspisR1Qm31ArithmeticProbe.field.M31.reduce_u64
    AspisR1Qm31ArithmeticProbe.field.reduce_u64
    aspis_core.field.P AspisR1Qm31ArithmeticProbe.field.P
  rfl

theorem reducer_total (x : U64) :
    ∃ z : U32, aspis_core.field.M31.reduce_u64 x = .ok z ∧
      z.val=x.val%2147483647 ∧ z.val<2147483647 := by
  rw [reducer_eq]
  exact AspisR1.ExtractedCurrentReducer.current_wrapper_mod x

/-- Full-U64 totality and exact canonical model equality for every lane. -/
theorem value_total_model (row : Row) :
    ∃ out : Q, value_owned row = .ok out ∧
      ∀ j : Fin 4, (coordinate out j).val=(rowAt row j).val%2147483647 ∧
        (coordinate out j).val<2147483647 := by
  obtain ⟨x0,h0,v0⟩ := WP.spec_imp_exists (Array.index_usize_spec row 0#usize (by simp [row.property]))
  obtain ⟨x1,h1,v1⟩ := WP.spec_imp_exists (Array.index_usize_spec row 1#usize (by simp [row.property]))
  obtain ⟨x2,h2,v2⟩ := WP.spec_imp_exists (Array.index_usize_spec row 2#usize (by simp [row.property]))
  obtain ⟨x3,h3,v3⟩ := WP.spec_imp_exists (Array.index_usize_spec row 3#usize (by simp [row.property]))
  obtain ⟨m0,r0,e0,c0⟩ := reducer_total x0
  obtain ⟨m1,r1,e1,c1⟩ := reducer_total x1
  obtain ⟨m2,r2,e2,c2⟩ := reducer_total x2
  obtain ⟨m3,r3,e3,c3⟩ := reducer_total x3
  refine ⟨⟨⟨m0,m1⟩,⟨m2,m3⟩⟩,?_,?_⟩
  · simp only [value_owned,h0,h1,h2,h3,r0,r1,r2,r3,bind_tc_ok]
  · intro j
    fin_cases j
    · simpa [coordinate,rowAt,v0] using And.intro e0 c0
    · simpa [coordinate,rowAt,v1] using And.intro e1 c1
    · simpa [coordinate,rowAt,v2] using And.intro e2 c2
    · simpa [coordinate,rowAt,v3] using And.intro e3 c3

/-- The newly emitted scalar is definitionally the S7 scalar already proved
against sourcePush, under its exact canonicality/phase invariant. -/
theorem residue_scalar_model (raw1 : U64) (limb basis : U32) (terms : Nat)
    (hl : limb.val<2^31-1) (hb : basis.val<2^31-1)
    (hr : raw1.val<2^34+(terms%4)*(2^31-2)^2) :
    ∃ result : U64,
      scalar_owned raw1 limb basis (decide (terms%4=3))=.ok result ∧
      result.val=AspisR1BatchedFoldSourceStep.sourcePush terms raw1.val (limb.val*basis.val) := by
  exact S7OwnedP6ScalarProof.scalar_eq_source_push raw1 limb basis terms hl hb hr

#print axioms reducer_eq
#print axioms reducer_total
#print axioms value_total_model
#print axioms residue_scalar_model
end S8OwnedP6ValueModel
