import R1Z.PV_OWNJ_DecodeWeight
import R1Z.PV_OWNJ_Rows
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_OWNJ_ValueBridge
open PV_OWNI_RawOps PV_OWNJ_DecodeFold
variable {K : Type} [Field K]

theorem entries_canon (decode : Q → K) (D : Decoder decode) (point : List Q)
 (hc : ∀ q ∈ point, Canon q) (width trailing suffix : Nat) :
 ∀ e ∈ PV_OWNI_BuildTotal.entries point width trailing suffix, Canon e.2 := by
 intro e he
 obtain ⟨pref,hp,rfl⟩ := List.mem_map.mp he
 exact (PV_OWNJ_DecodeWeight.weight decode D width pref (point.take width) (one,0)
  D.one_canon (fun q hq => hc q (List.mem_of_mem_take hq))).1

/-- Ordered sparse field fold at exactly the scanner's width, trailing and
suffix. The concrete Decoder instance and dense row transport remain open. -/
def sparse (decode : Q → K) (point column : List Q) : K :=
 (PV_OWNI_BuildTotal.entries point (PV_OWNI_Scanner.width point)
  (PV_OWNI_Scanner.trailing point) (PV_OWNI_Scanner.suffix point)).foldl
 (fun sum e => sum + decode e.2 * decode (column[e.1]?.getD zero)) 0

theorem value_commutes (decode : Q → K) (D : Decoder decode) (point column : List Q)
 (hp : ∀ q ∈ point, Canon q) (hc : ∀ q ∈ column, Canon q) :
 (PV_OWNI_RawConsumer.value point column (PV_OWNI_Scanner.width point)
  (PV_OWNI_Scanner.trailing point) (PV_OWNI_Scanner.suffix point)).map decode =
 if column.length ≠ 1024 then none else some (sparse decode point column) := by
 unfold PV_OWNI_RawConsumer.value
 split
 · rfl
 · rename_i h
   have hv := PV_OWNJ_DecodeFold.fold decode D column
    (PV_OWNI_BuildTotal.entries point (PV_OWNI_Scanner.width point)
     (PV_OWNI_Scanner.trailing point) (PV_OWNI_Scanner.suffix point)) zero D.zero_canon
    (fun e he => ⟨entries_canon decode D point hp _ _ _ e he, by
      cases hx : column[e.1]? with
      | none => exact D.zero_canon
      | some q => exact hc q (List.mem_of_getElem? hx)⟩)
   simp only [Option.map_some]
   rw [hv.2,D.zero_eq]
   rfl

#print axioms entries_canon
#print axioms value_commutes
end R1Z.PV_OWNJ_ValueBridge
