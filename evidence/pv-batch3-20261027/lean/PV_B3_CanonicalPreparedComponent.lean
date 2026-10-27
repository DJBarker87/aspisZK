import PV_B3_CanonicalSource
import PV_B3_CanonicalIndexTotal
import PV_B3_CanonicalMul
import PV_B3_CanonicalAdd
import PV_B3_CanonicalSub
set_option autoImplicit false
namespace PV_B3_Canonical
open Aeneas Aeneas.Std Result PV_B3_Copy_117
abbrev PreparedComponent := PV_B3_Copy_117.host_arithmetic.prepared_component_mul
 theorem prepared_component (left : Array U32 3#usize) (right : aspis_core.field.CM31) (hr : C right) :
    ∃ z, PreparedComponent left right = .ok z ∧ C z := by
  obtain ⟨a,ha⟩ := index_total left 0#usize (by decide)
  obtain ⟨b,hb⟩ := index_total left 1#usize (by decide)
  obtain ⟨c,hc⟩ := index_total left 2#usize (by decide)
  obtain ⟨m0,hm0,hcm0⟩ := current_mul a right.a
  obtain ⟨m1,hm1,hcm1⟩ := current_mul b right.b
  obtain ⟨s,hs,hcs⟩ := current_add right.a right.b hr.1 hr.2
  obtain ⟨m2,hm2,hcm2⟩ := current_mul c s
  obtain ⟨d,hd,hcd⟩ := current_sub m0 m1 hcm0 hcm1
  obtain ⟨e,he,hce⟩ := current_sub m2 m0 hcm2 hcm0
  obtain ⟨f,hf,hcf⟩ := current_sub e m1 hce hcm1
  refine ⟨⟨d,f⟩,?_,hcd,hcf⟩
  change (do
    let aa ← Array.index_usize left 0#usize
    let u ← S.mul aa right.a
    let bb ← Array.index_usize left 1#usize
    let v ← S.mul bb right.b
    let cc ← Array.index_usize left 2#usize
    let sum ← S.add right.a right.b
    let w ← S.mul cc sum
    let outa ← S.sub u v
    let mid ← S.sub w u
    let outb ← S.sub mid v
    ok (aspis_core.field.CM31.mk outa outb)) = _
  simp only [ha,hb,hc,hm0,hm1,hs,hm2,hd,he,hf,bind_tc_ok]
#print axioms prepared_component
end PV_B3_Canonical
