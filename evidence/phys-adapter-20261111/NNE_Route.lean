import NNE_Dispatch
import NNE_Snapshot
set_option autoImplicit false
noncomputable section
namespace NNE_Route
open Aeneas Aeneas.Std AspisR1 S2W_ReturnedCheckpoint

theorem byte_injective : Function.Injective nativeByte := by
 intro a b h
 apply UScalar.eq_of_val_eq
 have hv := congrArg UInt8.toNat h
 simpa only [nativeByte,UInt8.toNat_ofNat_of_lt' a.bv.isLt,
   UInt8.toNat_ofNat_of_lt' b.bv.isLt] using hv

theorem bytes_eq (xs ys : List U8) : xs.map nativeByte = ys.map nativeByte ↔ xs = ys := by
 exact ⟨fun h => List.map_injective byte_injective h,fun h => congrArg (List.map nativeByte) h⟩

theorem stage1 (data : Slice U8) :
 Hiq_ReleaseRoute.stage1 data ↔ nativeBytes data = [3,10] ∨ nativeBytes data = [3,11] := by
 change (data.val = [3#u8,10#u8] ∨ data.val = [3#u8,11#u8]) ↔ _
 have h10 : ([3,10] : List UInt8) = [3#u8,10#u8].map nativeByte := rfl
 have h11 : ([3,11] : List UInt8) = [3#u8,11#u8].map nativeByte := rfl
 simp only [nativeBytes,h10,h11,bytes_eq]

theorem asq8 (data : Slice U8) :
 Hiq_ReleaseRoute.asq8 data ↔ (nativeBytes data).take 4 = RSL.REQUEST_MAGIC := by
 change data.val.take 4 = [65#u8,83#u8,81#u8,56#u8] ↔ _
 have hm : RSL.REQUEST_MAGIC = [65#u8,83#u8,81#u8,56#u8].map nativeByte := rfl
 rw [hm]
 simp only [nativeBytes,← List.map_take,bytes_eq]

theorem first_guard (program : RSL.B32) (accounts : List RSL.AccountInfo) (data : Slice U8) :
 RSL.TX1_344.badRoute ⟨program,accounts,nativeBytes data⟩ = false ↔
 Hiq_ReleaseRoute.stage1 data ∧ accounts.length = 3 := by
 rw [stage1]
 simp [RSL.TX1_344.badRoute]

theorem second_guard (program : RSL.B32) (accounts : List RSL.AccountInfo) (data : Slice U8) :
 RSL.TX2_240.badRoute ⟨program,accounts,nativeBytes data⟩ = false ↔
 Hiq_ReleaseRoute.asq8 data ∧ accounts.length = 7 := by
 rw [asq8]
 constructor
 · intro h
   simp only [RSL.TX2_240.badRoute,Bool.or_eq_false_iff,bne_eq_false_iff_eq,
    decide_eq_false_iff_not] at h
   exact ⟨h.2,h.1.1⟩
 · intro h
   have len := congrArg List.length h.1
   have bound : 4 ≤ (nativeBytes data).length := by
    simp only [List.length_take,RSL.REQUEST_MAGIC,List.length_cons,List.length_nil] at len
    omega
   simp [RSL.TX2_240.badRoute,h.1,h.2,Nat.not_lt_of_ge bound]
#print axioms byte_injective
#print axioms bytes_eq
#print axioms stage1
#print axioms asq8
#print axioms first_guard
#print axioms second_guard
end NNE_Route
end
