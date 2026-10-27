import LPq_TowerPorts
import XRy_LoopWide
set_option autoImplicit false
namespace AspisR1.LPq_WidePorts
open Aeneas Aeneas.Std Result LPi_FieldValues LPq_FieldPorts XRo_Join_Carriers

theorem canonical (x : NE) (hx : canonE x) : XRy_WideMultiply.Canonical (wide x) := hx

theorem mul (x y : NE) (hx : canonE x) (hy : canonE y) :
    ∃ z, FIo_Native.aspis_core.field.wide_exact.WideExact.mul x y=ok z ∧ canonE z ∧
      aspis_core.field.wide_exact.WideExact.mul (wide x) (wide y)=ok (wide z) := by
  obtain ⟨ac,hac,cac,eac⟩ := LPq_TowerPorts.mul x.c0 y.c0 hx.1 hy.1
  obtain ⟨bd,hbd,cbd,ebd⟩ := LPq_TowerPorts.mul x.c1 y.c1 hx.2 hy.2
  obtain ⟨a,ha,ca,ea⟩ := LPq_TowerPorts.add x.c0 x.c1 hx.1 hx.2
  obtain ⟨b,hb,cb,eb⟩ := LPq_TowerPorts.add y.c0 y.c1 hy.1 hy.2
  obtain ⟨cross,hcross,ccross,ecross⟩ := LPq_TowerPorts.mul a b ca cb
  obtain ⟨u,hu,cu,eu⟩ := LPq_TowerPorts.mul_u bd cbd
  obtain ⟨lo,hlo,clo,elo⟩ := LPq_TowerPorts.add ac u cac cu
  obtain ⟨d,hd,cd,ed⟩ := LPq_TowerPorts.sub cross ac ccross cac
  obtain ⟨hi,hhi,chi,ehi⟩ := LPq_TowerPorts.sub d bd cd cbd
  refine ⟨⟨lo,hi⟩,?_,⟨clo,chi⟩,?_⟩
  · simp only [FIo_Native.aspis_core.field.wide_exact.WideExact.mul,
      hac,hbd,ha,hb,hcross,hu,hlo,hd,hhi,bind_tc_ok]
  · change (do
      let ac ← XRn_Join_Field.field.QM31.mul (qm x.c0) (qm y.c0)
      let bd ← XRn_Join_Field.field.QM31.mul (qm x.c1) (qm y.c1)
      let a ← XRn_Join_Field.field.QM31.add (qm x.c0) (qm x.c1)
      let b ← XRn_Join_Field.field.QM31.add (qm y.c0) (qm y.c1)
      let cross ← XRn_Join_Field.field.QM31.mul a b
      let u ← XRn_Join_Field.field.wide_exact.mul_u bd
      let lo ← XRn_Join_Field.field.QM31.add ac u
      let d ← XRn_Join_Field.field.QM31.sub cross ac
      let hi ← XRn_Join_Field.field.QM31.sub d bd
      ok (⟨XRn_Join_FieldExternal.oldQ lo,XRn_Join_FieldExternal.oldQ hi⟩ : C.E)) = _
    simp only [eac,ebd,ea,eb,ecross,eu,elo,ed,ehi,bind_tc_ok]
    rfl

theorem loop_mul (x y : NE) (hx : canonE x) (hy : canonE y) :
    ∃ z, FIo_Native.aspis_core.field.wide_exact.WideExact.mul x y=ok z ∧ canonE z ∧
      AspisR1LoopPowers.field.WideExact.mul (XRy_LoopWide.toLoop (wide x))
        (XRy_LoopWide.toLoop (wide y))=ok (XRy_LoopWide.toLoop (wide z)) := by
  obtain ⟨z,native,cz,release⟩ := mul x y hx hy
  obtain ⟨other,actual,_,model⟩ := XRy_LoopWide.multiply (wide x) (wide y)
    (canonical x hx) (canonical y hy)
  have same : other=wide z := Result.ok.inj (actual.symm.trans release)
  rw [same] at model
  exact ⟨z,native,cz,model⟩

#print axioms canonical
#print axioms mul
#print axioms loop_mul
end AspisR1.LPq_WidePorts
