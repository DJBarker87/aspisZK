import FJe_PackedRawOrigins
import FJe_PackedInputWords
import FJe_PackedRawAfterValue
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJe_PackedRawValue
open Aeneas Aeneas.Std Result FIq_Native
open FIv_NativeArithmetic (NQ)
open FIw_ArrayValue (canonical)
open FJb_TailCell (cell)
open AspisV8R15.ExactTowerBase (P)
def matrix (input : Array NQ 4#usize) (r j : Fin 4) : Nat :=
  RawPoseidonExternalRows.rawRowNat
    (fun k=>FJe_PackedRawRowValue.words (FJe_PackedInputWords.mapped input) k j) r
/-- Complete ORIGINAL raw packing VALUE. Every matrix cell and the offset are
derived from this call;no independently chosen table or output is assumed. -/
theorem value (input : Array NQ 4#usize) (out : Array U64 4#usize)
    (hc : canonical input) (run : state_only_poseidon.external_local_packed_raw input=ok out) :
    ∀ j : Fin 4,(cell out j).val=PoseidonExternalPackedAlgebra.packedNat (7*P) (matrix input) j := by
  obtain ⟨mapped,table,bound,hm,ht,hb,tail⟩ := FJe_PackedRawOrigins.value input out run
  have em : mapped=FJe_PackedInputWords.mapped input := FJb_LimbMap.value input mapped hm
  subst mapped
  have vt := FJe_PackedRawTable.value (FJe_PackedInputWords.mapped input) table ht
  obtain ⟨b,rb,vb,wide⟩ := FJe_PackedBound.value
  have eb : bound=b := Result.ok.inj (hb.symm.trans rb)
  subst b
  have tableBound : ∀ r j,(FJe_PackedRawAfter.words table r j).val<bound.val := by
    intro r j
    change (cell (cell table r) j).val<bound.val
    rw [vt r j,vb]
    exact FJe_RawReference.row_bounds _ (FJe_PackedInputWords.bounded input hc) r j
  have tableValue : (fun r j=>(FJe_PackedRawAfter.words table r j).val)=matrix input := by
    funext r j
    exact vt r j
  have v := FJe_PackedRawAfterValue.value table bound out tableBound wide tail
  intro j
  have vj := v j
  rw [vb,tableValue] at vj
  exact vj
#print axioms value
end AspisR1.FJe_PackedRawValue
end
