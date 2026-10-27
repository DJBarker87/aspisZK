import XRl_WideCanonical
open Aeneas Aeneas.Std Result
open XRk_Release XRk_FieldExternal XRk_ResultTools
namespace XRl_CanonicalConstructors
/-- Each successful native-library remainder is below P, including arbitrary
raw 32-bit representatives supplied to the validating constructor. -/
theorem remainder (x y : U32) (run : x % 2147483647#u32=ok y) : y<2147483647#u32 := by
  obtain ⟨z,hz,hval⟩ := WP.spec_imp_exists
    (UScalar.rem_spec (x:=x) (y:=2147483647#u32) (by scalar_tac))
  have same := Result.ok.inj (hz.symm.trans run)
  subst z
  change y.val<(2147483647#u32).val
  rw [hval]
  exact Nat.mod_lt _ (by scalar_tac)
theorem canon (x y : aspis_core.field.QM31) (run : XRk_FieldExternal.canon x=ok y) :
    XRk_CanonicalScalar.Canonical y := by
  unfold XRk_FieldExternal.canon at run
  obtain ⟨a,ha,run⟩ := bind_success _ _ _ run
  obtain ⟨b,hb,run⟩ := bind_success _ _ _ run
  obtain ⟨c,hc,run⟩ := bind_success _ _ _ run
  obtain ⟨d,hd,run⟩ := bind_success _ _ _ run
  have same := Result.ok.inj run
  subst y
  exact ⟨remainder x.c0.a a ha,remainder x.c0.b b hb,
    remainder x.c1.a c hc,remainder x.c1.b d hd⟩

theorem new (x y : aspis_core.field.QM31) (e : XRk_Wide)
    (run : aspis_core.field.wide_exact.WideExact.new x y=ok e) : XRl_WideCanonical.Canonical e := by
  unfold aspis_core.field.wide_exact.WideExact.new at run
  obtain ⟨a,ha,run⟩ := bind_success _ _ _ run
  obtain ⟨b,hb,run⟩ := bind_success _ _ _ run
  have same := Result.ok.inj run
  subst e
  exact ⟨canon x a ha,canon y b hb⟩

theorem from_qm31 (x : aspis_core.field.QM31) (e : XRk_Wide)
    (run : aspis_core.field.wide_exact.WideExact.from_qm31 x=ok e) : XRl_WideCanonical.Canonical e :=
  new x qzero e run

#print axioms canon
#print axioms new
#print axioms from_qm31
#print axioms remainder
end XRl_CanonicalConstructors
