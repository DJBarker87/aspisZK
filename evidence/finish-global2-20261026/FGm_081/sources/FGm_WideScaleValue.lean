import FGm_QMScaleValue
set_option autoImplicit false
noncomputable section
namespace AspisR1.FGm_WideScaleValue
open Aeneas Aeneas.Std Result AspisR1CurrentWide.Proof
open FIo_FieldBridge (NC NQ NE cm qm wide)

theorem value (x z : NE) (y : U32)
    (run : FIo_Native.aspis_core.field.wide_exact.WideExact.mul_m31 x y=ok z) :
    FIo_WideValues.Canon z ∧ decodeWide (wide z)=decodeM y • decodeWide (wide x) := by
  unfold FIo_Native.aspis_core.field.wide_exact.WideExact.mul_m31 at run
  obtain ⟨scalar,hscalar,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨a,ha,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨b,hb,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  have same : (⟨a,b⟩ : NE)=z := Result.ok.inj run
  subst z
  have va := FGm_QMScaleValue.value x.c0 a scalar ha
  have vb := FGm_QMScaleValue.value x.c1 b scalar hb
  have scalarValue : decodeM scalar=decodeM y := by
    have nonzero : FIo_Native.aspis_core.field.P.val≠0 := by decide
    obtain ⟨rem,hr,hv⟩ := Aeneas.Std.WP.spec_imp_exists (UScalar.rem_spec y nonzero)
    have same : rem=scalar := Result.ok.inj (hr.symm.trans hscalar)
    subst rem
    have v : scalar.val=y.val%2147483647 := hv
    change (scalar.val : ZMod 2147483647) = (y.val : ZMod 2147483647)
    rw [v,ZMod.natCast_mod]
  refine ⟨⟨va.1,vb.1⟩,?_⟩
  apply QuadraticAlgebra.ext
  · change decodeQM (qm a)=decodeM y • decodeQM (qm x.c0)
    rw [←scalarValue]
    exact va.2
  · change decodeQM (qm b)=decodeM y • decodeQM (qm x.c1)
    rw [←scalarValue]
    exact vb.2

#print axioms value
end AspisR1.FGm_WideScaleValue
end
