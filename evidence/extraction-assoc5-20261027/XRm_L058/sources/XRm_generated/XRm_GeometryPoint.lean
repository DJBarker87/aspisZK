import XRm_FieldCanonical
import XRk_Funs
open Aeneas Aeneas.Std Result
open XRk_Release XRk_ResultTools XRm_FieldCanonical
namespace XRm_GeometryPoint
/-- Source-selected table lookup and complex multiplication. The two large
tables remain symbolic; the theorem does not normalize their entries. -/
theorem point (u : aspis_core.r0.domain.FibreIndex)
    (out : aspis_core.r0.domain.Point aspis_core.field.M31)
    (run : fast_domain.fibre_point u=ok out) :
    ∃ high a b left right product,
      u >>> 9#i32=ok high ∧
      Array.index_usize fast_domain.TABLE_A (u &&& 511#usize)=ok a ∧
      Array.index_usize fast_domain.TABLE_B high=ok b ∧
      fast_domain.table_value a=ok left ∧ fast_domain.table_value b=ok right ∧
      aspis_core.field.CM31.mul left right=ok product ∧
      out.x=product.a ∧ out.y=product.b ∧ M out.x ∧ M out.y := by
  unfold fast_domain.fibre_point at run
  simp only [aspis_core.r0.domain.FibreIndex.get,lift,bind_tc_ok] at run
  obtain ⟨a,ha,run⟩ := bind_success _ _ _ run
  obtain ⟨left,hl,run⟩ := bind_success _ _ _ run
  obtain ⟨high,hh,run⟩ := bind_success _ _ _ run
  obtain ⟨b,hb,run⟩ := bind_success _ _ _ run
  obtain ⟨right,hr,run⟩ := bind_success _ _ _ run
  obtain ⟨product,hp,run⟩ := bind_success _ _ _ run
  have same := Result.ok.inj run
  subst out
  have hc := cmul left right product hp
  exact ⟨high,a,b,left,right,product,hh,ha,hb,hl,hr,hp,rfl,rfl,hc.1,hc.2⟩

theorem table_value (a b : U32) :
    fast_domain.table_value (a,b)=ok (⟨a,b⟩ : aspis_core.field.CM31) := by rfl

theorem low_index (u : Usize) : (u &&& 511#usize).val=u.val%512 := by
  rw [UScalar.val_and]
  change u.val &&& (2^9-1)=u.val%2^9
  exact Nat.and_two_pow_sub_one_eq_mod u.val 9

theorem line (u : aspis_core.r0.domain.FibreIndex) (out : aspis_core.field.M31)
    (run : fast_domain.line_node u=ok out) :
    ∃ p square double,
      fast_domain.fibre_point u=ok p ∧ aspis_core.field.M31.mul p.x p.x=ok square ∧
      aspis_core.field.M31.double square=ok double ∧
      aspis_core.field.M31.sub double 1#u32=ok out ∧ M out := by
  unfold fast_domain.line_node at run
  obtain ⟨p,hp,run⟩ := bind_success _ _ _ run
  obtain ⟨square,hs,run⟩ := bind_success _ _ _ run
  obtain ⟨double,hd,run⟩ := bind_success _ _ _ run
  simp only [aspis_core.field.M31.ONE,bind_tc_ok] at run
  have cs := mul _ _ _ hs
  have cd := XRm_M31Canonical.add _ _ _ cs cs hd
  have co := XRm_M31Canonical.sub _ _ _ cd (by scalar_tac) run
  exact ⟨p,square,double,hp,hs,hd,run,co⟩
#print axioms point
#print axioms table_value
#print axioms low_index
#print axioms line
end XRm_GeometryPoint
