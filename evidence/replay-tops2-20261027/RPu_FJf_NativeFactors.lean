import RPu_FJf_ModelPoint
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJf_NativeFactors
open Aeneas Aeneas.Std Result AspisR1CurrentWide.Proof
open FIo_FieldBridge (NQ qm)
open FJc_WeightQMBridge (SQ)
abbrev Factors := Array (Array (Array NQ 4#usize) 5#usize) 5#usize

def digitValue (a : Array NQ 4#usize) (s : Nat) : OraclePortCheckpointAbiC5.K :=
  match a.val[s]? with | some x => decodeQM (qm x) | none => 0

def rowValue (a : Array (Array NQ 4#usize) 5#usize) (d s : Nat) : OraclePortCheckpointAbiC5.K :=
  match a.val[d]? with | some x => digitValue x s | none => 0

def value (a : Factors) (k d s : Nat) : OraclePortCheckpointAbiC5.K :=
  match a.val[k]? with | some x => rowValue x d s | none => 0

theorem digit_map (a : Array SQ 4#usize) (s : Nat) :
    digitValue (FIn_WeightsInstall.mapArray FIo_Install.toQ a) s=FJc_WeightArray.value a s := by
  simp only [digitValue,FJc_WeightArray.value,FIn_WeightsInstall.mapArray,List.getElem?_map]
  cases a.val[s]? <;> rfl

theorem row_map (a : FJf_FactorArray.Row) (d s : Nat) :
    rowValue (FIn_WeightsInstall.mapArray (FIn_WeightsInstall.mapArray FIo_Install.toQ) a) d s=
      FJf_FactorArray.rowValue a d s := by
  simp only [rowValue,FJf_FactorArray.rowValue,FIn_WeightsInstall.mapArray,List.getElem?_map]
  cases h : a.val[d]? with
  | none => rfl
  | some x => exact digit_map x s

theorem factors_map (a : FJf_PointBody.Factors) (k d s : Nat) :
    value (FIn_WeightsInstall.mapArray
      (FIn_WeightsInstall.mapArray (FIn_WeightsInstall.mapArray FIo_Install.toQ)) a) k d s=
      FJf_FactorArray.value a k d s := by
  simp only [value,FJf_FactorArray.value,FIn_WeightsInstall.mapArray,List.getElem?_map]
  cases h : a.val[k]? with
  | none => rfl
  | some x => exact row_map x d s

theorem read (a : Factors) (k d s : Usize)
    (row : Array (Array NQ 4#usize) 5#usize) (digit : Array NQ 4#usize) (x : NQ)
    (hr : Array.index_usize a k=ok row) (hd : Array.index_usize row d=ok digit)
    (hs : Array.index_usize digit s=ok x) : value a k.val d.val s.val=decodeQM (qm x) := by
  simp only [value,rowValue,digitValue,FJc_ReadSlot.slot _ _ _ hr,
    FJc_ReadSlot.slot _ _ _ hd,FJc_ReadSlot.slot _ _ _ hs]

#print axioms digit_map
#print axioms row_map
#print axioms factors_map
#print axioms read
end AspisR1.FJf_NativeFactors
end
