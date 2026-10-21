import S7OwnedP6RowContract
import S7OwnedP6LoopSimulation

/-! Exact partial S7 residue obligation. Total on a typed invariant domain;
the frozen Vec caller must construct that domain independently. This does
not assert all-storage totality or complete query_values correspondence. -/
set_option autoImplicit false
namespace AspisR1.OraclePortJoinSplitS7
open Aeneas Aeneas.Std Result

structure ResidueArgs where
  raw : U64
  limb : U32
  basis : U32
  terms : Nat
  limbCanonical : limb.val < 2^31-1
  basisCanonical : basis.val < 2^31-1
  cadence : raw.val < 2^34 + (terms%4) * (2^31-2)^2

theorem residue_total (a : ResidueArgs) :
    ∃ result : U64,
      S7OwnedP6Scalar.residue_scalar_owned a.raw a.limb a.basis
        (decide (a.terms%4=3)) = ok result ∧
      result.val = AspisR1BatchedFoldSourceStep.sourcePush a.terms a.raw.val
        (a.limb.val*a.basis.val) :=
  S7OwnedP6ScalarProof.scalar_eq_source_push a.raw a.limb a.basis a.terms
    a.limbCanonical a.basisCanonical a.cadence

/-- Local four-lane source/model equality already proved by the partial P6
packet. The enclosing 64-weight/basis/Vec traversal is still owed. -/
theorem row_join (raw limbs : S7OwnedP6RowContract.Row) (basis terms : Nat) :
    S7OwnedP6RowContract.source raw limbs basis (decide (terms%4=3)) =
      fun j => AspisR1BatchedFoldSourceStep.sourcePush terms (raw j) (limbs j*basis) :=
  S7OwnedP6RowContract.source_eq_batched_model raw limbs basis terms

#print axioms residue_total
#print axioms row_join
end AspisR1.OraclePortJoinSplitS7
