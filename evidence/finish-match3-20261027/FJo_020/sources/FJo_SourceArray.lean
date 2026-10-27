import FJo_SourceCoordinate
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJo_SourceArray
open Aeneas Aeneas.Std Result
open AspisR1ClaimPreparedBridge AspisR1CurrentCaller.InstalledPreparation
open AspisR1CurrentPreparedClaim.Concrete
abbrev P := FJo_SourceCoordinate.P
/-- Lift source cells to the exact native array selected by the TX1 query. -/
theorem value (rs : Array P 29#usize) (gamma : E)
    (cells : ∀ i : Usize,i.val<29 → ∃ v,
      Array.index_usize (mapArray toClaimE rs) i=ok v ∧ Canonical v ∧ decode v=gamma^i.val) :
    let native := FIp_DotsAdapter.toArray (Tx1Q_Carriers.arr Tx1Q_Carriers.e (mapArray currentE rs))
    FIo_ArrayCanon.Holds native ∧ ∀ j : Fin 29,FIp_ArrayValue.value native j.val=gamma^j.val := by
  let native := FIp_DotsAdapter.toArray (Tx1Q_Carriers.arr Tx1Q_Carriers.e (mapArray currentE rs))
  have coordinate (j : Fin 29) :
      FIo_WideValues.Canon (FIo_Install.toE (Tx1Q_Carriers.e (currentE (rs.val[j.val]'(by rw [rs.property];exact j.isLt))))) ∧
      FIp_ArrayValue.value native j.val=gamma^j.val := by
    let i : Usize := Usize.ofNat j.val (by have:=j.isLt;scalar_tac)
    obtain ⟨v,read,canonical,meaning⟩ := cells i j.isLt
    have slot := FJc_ReadSlot.slot _ _ _ read
    change (rs.val.map toClaimE)[j.val]?=some v at slot
    rw [List.getElem?_map,List.getElem?_eq_getElem (by rw [rs.property];exact j.isLt)] at slot
    have same := Option.some.inj slot
    subst v
    refine ⟨FJo_SourceCoordinate.canonical _ canonical,?_⟩
    unfold native FIp_ArrayValue.value FIp_DotsAdapter.toArray Tx1Q_Carriers.arr mapArray
    simp only [List.getElem?_map,List.getElem?_eq_getElem (by rw [rs.property];exact j.isLt),Option.map_some]
    exact (FJo_SourceCoordinate.value _).trans meaning
  constructor
  · intro x hx
    obtain ⟨y,hy,rfl⟩ := List.mem_map.mp hx
    obtain ⟨z,hz,rfl⟩ := List.mem_map.mp hy
    obtain ⟨w,hw,rfl⟩ := List.mem_map.mp hz
    obtain ⟨n,hn,eq⟩ := List.mem_iff_getElem.mp hw
    have bound : n<29 := by simpa only [rs.property] using hn
    simpa only [eq] using (coordinate ⟨n,bound⟩).1
  · intro j; exact (coordinate j).2
#print axioms value
end AspisR1.FJo_SourceArray
end
