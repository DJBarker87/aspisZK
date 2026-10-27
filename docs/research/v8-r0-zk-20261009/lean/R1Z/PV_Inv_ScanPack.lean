import R1Z.PV_Inv_Scan
import R1Z.PV_Inv_PackOperands
set_option autoImplicit false
namespace R1Z.PV_Inv_ScanPack
open PV_Inv_Pack PV_Inv_PackList PV_Inv_PackOperands
variable {K : Type} [Field K] [DecidableEq K]

theorem guard_to_operands (chi : K) (es : List (Endpoint K)) (s : Slots K)
    (guard : PV_Inv_Scan.scan chi true (es.map Endpoint.value) = true)
    (packing : run empty es = some s) : ∀ d ∈ operands chi s, d ≠ 0 := by
  apply packed_nonzero chi es s _ packing
  intro e he
  exact ((PV_Inv_Scan.scan_iff chi true _).mp guard).2 e.value (List.mem_map.mpr ⟨e,he,rfl⟩)

theorem guard_excludes_none (chi : K) (es : List (Endpoint K)) (s : Slots K)
    (guard : PV_Inv_Scan.scan chi true (es.map Endpoint.value) = true)
    (packing : run empty es = some s) :
    ∀ d ∈ operands chi s, PV_Inv_Guard.checkedInverse d ≠ none := by
  intro d hd hn
  exact guard_to_operands chi es s guard packing d hd ((PV_Inv_Guard.none_iff d).mp hn)

#print axioms guard_to_operands
#print axioms guard_excludes_none
end R1Z.PV_Inv_ScanPack
