import R1Z.PV_OWNK_QMDecode
import R1Z.PV_OWNJ_ValueBridge
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_OWNK_ConcreteDecoder
open Aeneas Aeneas.Std Result
open PV_OWNI_RawOps
abbrev decode := PV_OWNK_QMDecode.decode
abbrev K := PV_OWNK_QMDecode.K
abbrev Canon := PV_OWNK_TowerCanon.Canon

theorem canon_iff (q : Q) : Canon q ↔ PV_OWNJ_DecodeFold.Canon q := by
 constructor
 · rintro ⟨⟨a,b⟩,⟨c,d⟩⟩; exact ⟨a,b,c,d⟩
 · rintro ⟨a,b,c,d⟩; exact ⟨⟨a,b⟩,c,d⟩

/-- Concrete instance: no Decoder field remains a hypothesis. -/
theorem decoder : PV_OWNJ_DecodeFold.Decoder decode := by
 constructor
 · exact PV_OWNK_QMDecode.zero
 · exact PV_OWNK_QMDecode.one
 · exact (canon_iff _).mp PV_OWNK_TowerCanon.zero_canon
 · exact (canon_iff _).mp PV_OWNK_TowerCanon.one_canon
 · intro x y hx hy
   exact ⟨(canon_iff _).mp (PV_OWNK_TowerCanon.qm_add _ _
    ((canon_iff _).mpr hx) ((canon_iff _).mpr hy)),
    PV_OWNK_QMDecode.add _ _ ((canon_iff _).mpr hx) ((canon_iff _).mpr hy)⟩
 · intro x y hx hy
   exact ⟨(canon_iff _).mp (PV_OWNK_TowerCanon.qm_mul _ _),
    PV_OWNK_QMDecode.mul _ _ ((canon_iff _).mpr hx) ((canon_iff _).mpr hy)⟩
 · intro x hx
   refine ⟨(canon_iff _).mp (PV_OWNK_TowerCanon.qm_sub _ _
    PV_OWNK_TowerCanon.one_canon ((canon_iff _).mpr hx)),?_⟩
   have h := PV_OWNK_QMDecode.sub one x PV_OWNK_TowerCanon.one_canon ((canon_iff _).mpr hx)
   rw [PV_OWNK_QMDecode.one] at h
   exact h

theorem value_commutes (point column : List Q)
 (hp : ∀ q ∈ point, Canon q) (hc : ∀ q ∈ column, Canon q) :
 (PV_OWNI_RawConsumer.value point column (PV_OWNI_Scanner.width point)
  (PV_OWNI_Scanner.trailing point) (PV_OWNI_Scanner.suffix point)).map decode =
 if column.length ≠ 1024 then none else some (PV_OWNJ_ValueBridge.sparse decode point column) :=
 PV_OWNJ_ValueBridge.value_commutes decode decoder point column
  (fun q h => (canon_iff _).mp (hp q h)) (fun q h => (canon_iff _).mp (hc q h))

/-- Complete value-phase Result, with exact scanner split and suffix. This
still concludes the ordered sparse value, not the unproved dense equation. -/
theorem source_commutes (point column : List Q) (hl : point.length = 10)
 (hp : ∀ q ∈ point, Canon q) (hc : ∀ q ∈ column, Canon q) :
 (do
  let value ← PV_OWNI_RawConsumer.source point column (PV_OWNI_Scanner.width point)
   (PV_OWNI_Scanner.trailing point) (PV_OWNI_Scanner.suffix point)
  ok (value.map decode)) =
 ok (if column.length ≠ 1024 then none else some (PV_OWNJ_ValueBridge.sparse decode point column)) := by
 rw [PV_OWNI_RawConsumer.result point column _ _ _
  (PV_OWNI_Scanner.split point hl) (PV_OWNI_Scanner.suffix_bound point)]
 simp only [bind_tc_ok]
 rw [value_commutes point column hp hc]
#print axioms canon_iff
#print axioms decoder
#print axioms value_commutes
#print axioms source_commutes
end R1Z.PV_OWNK_ConcreteDecoder
