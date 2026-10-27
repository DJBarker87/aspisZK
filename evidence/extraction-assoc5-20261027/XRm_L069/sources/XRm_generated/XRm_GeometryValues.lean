import XRm_FieldValues
import XRm_GeometryPoint
open Aeneas Aeneas.Std Result
open XRk_Release XRk_ResultTools XRm_FieldValues XRm_FieldCanonical
namespace XRm_GeometryValues
abbrev F := XRm_FieldValues.M31Exact
/-- The actual line-node source arithmetic has the stated field meaning,
with canonical output. This says nothing about the geometric table identity
or allocator/native effects. -/
theorem line (u : aspis_core.r0.domain.FibreIndex) (out : aspis_core.field.M31)
    (run : fast_domain.line_node u=ok out) :
    ∃ p, fast_domain.fibre_point u=ok p ∧
      (out.val:F)=2*(p.x.val:F)^2-1 ∧ M out := by
  obtain ⟨p,square,double,hp,hs,hd,ho,hcanonical⟩ := XRm_GeometryPoint.line u out run
  have cs := XRm_FieldCanonical.mul _ _ _ hs
  have cd := XRm_M31Canonical.add _ _ _ cs cs hd
  have vs := XRm_FieldValues.mul _ _ _ hs
  have vd := XRm_FieldValues.add _ _ _ cs cs hd
  have vo := XRm_FieldValues.sub _ _ _ cd (by scalar_tac) ho
  refine ⟨p,hp,?_,hcanonical⟩
  rw [vo,vd,vs]
  change (p.x.val:F)*(p.x.val:F)+(p.x.val:F)*(p.x.val:F)-1=2*(p.x.val:F)^2-1
  ring

/-- The SAME square/double/sub operations also compute the query line-z
lane. The line-x input can be any raw word; multiplication reduces it. -/
theorem z (x square double out : aspis_core.field.M31)
    (hs : aspis_core.field.M31.mul x x=ok square)
    (hd : aspis_core.field.M31.double square=ok double)
    (ho : aspis_core.field.M31.sub double 1#u32=ok out) :
    (out.val:F)=2*(x.val:F)^2-1 ∧ M out := by
  have cs := XRm_FieldCanonical.mul _ _ _ hs
  have cd := XRm_M31Canonical.add _ _ _ cs cs hd
  have vs := XRm_FieldValues.mul _ _ _ hs
  have vd := XRm_FieldValues.add _ _ _ cs cs hd
  have vo := XRm_FieldValues.sub _ _ _ cd (by scalar_tac) ho
  refine ⟨?_,XRm_M31Canonical.sub _ _ _ cd (by scalar_tac) ho⟩
  rw [vo,vd,vs]
  change (x.val:F)*(x.val:F)+(x.val:F)*(x.val:F)-1=2*(x.val:F)^2-1
  ring
#print axioms line
#print axioms z
end XRm_GeometryValues
