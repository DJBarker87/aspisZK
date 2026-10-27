import RPu_FJj_TensorTwo
import RPu_FJj_HighProductInstances
import RPu_FJg_TensorProduct
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJr_RowTensor
open Aeneas Aeneas.Std Result
open FIo_FieldBridge (NQ)
abbrev FK := OraclePortCheckpointAbiC5.K
abbrev FE := OraclePortCheckpointAbiC5.E
attribute [local irreducible] QuadraticAlgebra.instInv

theorem high (row : Array (Array NQ 4#usize) 5#usize) (factors : Fin 5 → Fin 4 → FK)
    (values : ∀ (d : Fin 5) (s : Fin 4),FJj_TensorPrefix.rowValue row d.val s.val=factors d s)
    (i : Fin 64) :
    FJj_TensorPrefix.prefixValue (FJj_TensorPrefix.rowValue row) 3 i.val=
      FJg_TensorProduct.high factors i := by
  have s2 : i.val%4<4 := Nat.mod_lt _ (by decide)
  have s3 : i.val/4%4<4 := Nat.mod_lt _ (by decide)
  have s4 : i.val/16<4 := by have:=i.isLt;omega
  have q2 : FJj_TensorPrefix.rowValue row 2 (i.val%4)=factors 2 ⟨_,s2⟩ := values 2 ⟨_,s2⟩
  have q3 : FJj_TensorPrefix.rowValue row 3 (i.val/4%4)=factors 3 ⟨_,s3⟩ := values 3 ⟨_,s3⟩
  have q4 : FJj_TensorPrefix.rowValue row 4 (i.val/16)=factors 4 ⟨_,s4⟩ := values 4 ⟨_,s4⟩
  have native : FJj_TensorPrefix.prefixValue (FJj_TensorPrefix.rowValue row) 3 i.val=
      FJj_HighProductInstances.product factors i := by
    rw [FJj_TensorPrefix.three,q2,q3,q4]
    rfl
  rw [native]
  exact FJj_HighProductInstances.tower AspisV8R15.ExactTowerBase.qm31R 0 factors i

theorem value (self : FIo_Native.weights.Weights) (idx : Usize)
    (row : Array (Array NQ 4#usize) 5#usize)
    (hr : Array.index_usize self.factors idx=ok row)
    (hc : ∀ digit∈row.val,FJf_QMArray.canon digit)
    (factors : Fin 5 → Fin 4 → FK)
    (values : ∀ (d : Fin 5) (s : Fin 4),FJj_TensorPrefix.rowValue row d.val s.val=factors d s)
    (input out : Slice NQ) (hs : FJj_QMSlice.canon input)
    (run : FIo_Native.weights.Weights.tensor self idx 2#usize input=ok out) :
    FJj_QMSlice.canon out ∧ out.val.length=input.val.length ∧ ∀ i : Fin 64,
      algebraMap FK FE (FJj_QMSlice.value out i.val)=
        FJg_TensorProduct.high (fun d s=>algebraMap FK FE (factors d s)) i := by
  obtain ⟨co,len,vs⟩ := FJj_TensorTwo.value self idx row hr hc input out hs run
  refine ⟨co,len,?_⟩
  intro i
  rw [vs i.val i.isLt,high row factors values i]
  exact FJj_HighProductInstances.map (algebraMap FK FE) factors i

#print axioms high
#print axioms value
end AspisR1.FJr_RowTensor
end
