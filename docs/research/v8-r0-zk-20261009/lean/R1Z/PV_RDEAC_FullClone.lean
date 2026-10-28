import R1Z.PV_RDEAC_FullAppend
open Aeneas Aeneas.Std
namespace R1Z.PV_RDEAC_FullClone
open PV_RDB1_V183_ReserveWorld PV_RDB1_Append

def clone {S F : Type} (step : Request → S → Option Nat × S)
    (shape : Shape) (address : Nat) (base : List U8) (w : World S F) : Execution U8 S F :=
  let e := PV_RDB1_V181.deployed step 18446744073709551615 9223372036854775807 shape address base.length w
  match h : e.returned with
  | .error _ => e
  | .ok () =>
    let b : Buffer U8 := ⟨e.buffer.address,e.buffer.capacity,base,by
      have hc := PV_RDEA_CloneExecution.capacity_success step shape address base.length w h
      exact Nat.le_of_eq hc.symm⟩
    ⟨.ok (),b,{e.world with memory:=writeTail e.buffer.address 0 base e.world.memory}⟩

theorem projection {S F : Type} (step : Request → S → Option Nat × S)
    (shape : Shape) (address : Nat) (base : List U8) (w : World S F) :
    PV_RDEAC_FullAppend.erase (clone step shape address base w)=PV_RDEA_CloneExecution.clone step shape address base w := by
  unfold clone PV_RDEA_CloneExecution.clone
  split <;> rename_i h
  · simp only [PV_RDEAC_FullAppend.erase,h]
  · rfl

theorem failed_capacity {S F : Type} (step : Request → S → Option Nat × S)
    (shape : Shape) (address : Nat) (base : List U8) (w : World S F)
    (err : PV_RDB1_V183_ReserveWorld.Error) (h : (clone step shape address base w).returned=.error err) :
    (clone step shape address base w).buffer.capacity=0 := by
  unfold clone at h ⊢
  split at h <;> rename_i hr
  · simp only [hr]
    unfold PV_RDB1_V181.deployed at hr ⊢
    split <;> try rfl
    split <;> try rfl
    split at hr <;> rename_i hz
    · cases hr
    · simp only [hz,if_false]
      unfold finish at hr ⊢
      dsimp only at hr ⊢
      cases hs : step ⟨address,0,base.length,shape⟩ w.allocator with
      | mk p s => cases p <;> simp [hs,PV_RDB1_V181.empty] at hr ⊢
  · cases h

#print axioms projection
#print axioms failed_capacity
end R1Z.PV_RDEAC_FullClone
