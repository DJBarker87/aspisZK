import CuSavingsWideCore
import ExtractedCurrentQM31Equality
import Mathlib.Tactic.Ring
set_option autoImplicit false
set_option maxRecDepth 2048
namespace AspisR1.CuSavingsWideArithmetic
open Aeneas Aeneas.Std Result AspisR1WideArithmetic

theorem m_sub_transport (x y : U32) : field.M31.sub x y =
    AspisR1Qm31ArithmeticProbe.field.M31.sub x y := by
  simp only [field.M31.sub,AspisR1Qm31ArithmeticProbe.field.M31.sub,
    field.P,AspisR1Qm31ArithmeticProbe.field.P]

theorem cm_sub_transport (x y : field.CM31) : field.CM31.sub x y =
    (do let z ← AspisR1Qm31ArithmeticProbe.field.CM31.sub (toC x) (toC y); .ok (fromC z)) := by
  simp only [field.CM31.sub,AspisR1Qm31ArithmeticProbe.field.CM31.sub,
    m_sub_transport,toC,fromC,bind_assoc_eq,bind_tc_ok]

theorem k_sub (x y : K) (hx : CanonicalK x) (hy : CanonicalK y) :
    ∃ z, field.QM31.sub x y=.ok z ∧ CanonicalK z ∧ decodeK z=decodeK x-decodeK y := by
  obtain ⟨a,ha,hac,hav,haw⟩ := ExtractedCurrentTowerAdd.current_cm_sub_mod (toC x.c0) (toC y.c0) hx.1 hy.1
  obtain ⟨b,hb,hbc,hbv,hbw⟩ := ExtractedCurrentTowerAdd.current_cm_sub_mod (toC x.c1) (toC y.c1) hx.2 hy.2
  refine ⟨⟨fromC a,fromC b⟩,?_,⟨hac,hbc⟩,?_⟩
  · simp only [field.QM31.sub,cm_sub_transport,ha,hb,bind_tc_ok]
  · have hw : ExtractedCurrentQM31Mul.wordsQM (toK ⟨fromC a,fromC b⟩) =
        AspisV8R17.GeneratedQM31Linear.qmSubWords
          (ExtractedCurrentQM31Mul.wordsQM (toK x)) (ExtractedCurrentQM31Mul.wordsQM (toK y)) :=
      Prod.ext (Prod.ext hav haw) (Prod.ext hbv hbw)
    change AspisV8R17.QM31WordTower.decodeQ (ExtractedCurrentQM31Mul.wordsQM (toK ⟨fromC a,fromC b⟩)) =
      AspisV8R17.QM31WordTower.decodeQ (ExtractedCurrentQM31Mul.wordsQM (toK x)) - AspisV8R17.QM31WordTower.decodeQ (ExtractedCurrentQM31Mul.wordsQM (toK y))
    rw [hw]
    exact AspisV8R17.QM31WordTower.decode_sub _ _ hy

theorem cm_r_transport (x : field.CM31) : field.mul_by_r x =
    (do let z ← AspisR1Qm31ArithmeticProbe.field.mul_by_r (toC x); .ok (fromC z)) := by
  simp only [field.mul_by_r,AspisR1Qm31ArithmeticProbe.field.mul_by_r,
    field.M31.double,AspisR1Qm31ArithmeticProbe.field.M31.double,
    field.M31.add,m_sub_transport,toC,fromC,bind_assoc_eq,bind_tc_ok]

theorem cm_r_words (x : CurrentC) (hx : ExtractedCurrentTowerAdd.CanonicalCM x) :
    ∃ z, AspisR1Qm31ArithmeticProbe.field.mul_by_r x=.ok z ∧
      ExtractedCurrentTowerAdd.CanonicalCM z ∧
      ExtractedCurrentTowerAdd.wordsCM z=ExtractedCurrentQM31Mul.rWords (ExtractedCurrentTowerAdd.wordsCM x) := by
  obtain ⟨a2,ea2,va2,ca2⟩ := ExtractedCurrentM31AddSub.current_add_mod x.a x.a hx.1 hx.1
  obtain ⟨a,ea,va,ca⟩ := ExtractedCurrentM31AddSub.current_sub_mod a2 x.b ca2 hx.2
  obtain ⟨b2,eb2,vb2,cb2⟩ := ExtractedCurrentM31AddSub.current_add_mod x.b x.b hx.2 hx.2
  obtain ⟨b,eb,vb,cb⟩ := ExtractedCurrentM31AddSub.current_add_mod x.a b2 hx.1 cb2
  refine ⟨⟨a,b⟩,?_,⟨ca,cb⟩,?_⟩
  · simp only [AspisR1Qm31ArithmeticProbe.field.mul_by_r,
      AspisR1Qm31ArithmeticProbe.field.M31.double,ea2,ea,eb2,eb,bind_tc_ok]
  · simp only [ExtractedCurrentTowerAdd.wordsCM,ExtractedCurrentQM31Mul.rWords]
    exact Prod.ext (by simpa only [va2] using va) (by simpa only [vb2] using vb)

theorem k_mul_u (x : K) (hx : CanonicalK x) :
    ∃ z, field.wide_exact.mul_u x=.ok z ∧ CanonicalK z ∧ decodeK z=U*decodeK x := by
  obtain ⟨c,hc,hcan,hw⟩ := cm_r_words (toC x.c1) hx.2
  refine ⟨⟨fromC c,x.c0⟩,?_,⟨hcan,hx.1⟩,?_⟩
  · simp only [field.wide_exact.mul_u,cm_r_transport,hc,bind_tc_ok]
  · have hr := congrArg AspisV8R17.QM31WordTower.embedC
      (AspisV8R17.QM31WordResidues.decode_r (ExtractedCurrentTowerAdd.wordsCM (toC x.c1)) hx.2)
    have hv : AspisV8R17.QM31WordTower.decodeC (ExtractedCurrentTowerAdd.wordsCM c) =
        AspisV8R17.QuadraticTowerOperations.r *
          AspisV8R17.QM31WordTower.decodeC (ExtractedCurrentTowerAdd.wordsCM (toC x.c1)) := by
      rw [hw]
      change AspisV8R17.QM31WordTower.decodeC
        (AspisV8R17.GeneratedQM31Products.rWords _) = _
      convert hr using 1 <;>
        ext <;> simp [AspisV8R17.QM31WordTower.decodeC,AspisV8R17.QM31WordTower.embedC,
          AspisV8R17.QM31WordResidues.cR,AspisV8R17.QM31WordResidues.decodeC,
          AspisV8R17.QuadraticTowerOperations.r, AspisV8R17.QuadraticTowerOperations.cr] <;> ring
    apply QuadraticAlgebra.ext
    · change AspisV8R17.QM31WordTower.decodeC (ExtractedCurrentTowerAdd.wordsCM c) = (U*decodeK x).re
      rw [QuadraticAlgebra.re_mul]
      simpa [U] using hv
    · change (decodeK x).re = (U*decodeK x).im
      simp [U,QuadraticAlgebra.im_mul]

theorem mul (x y : E) (hx : CanonicalE x) (hy : CanonicalE y) :
    ∃ z, field.wide_exact.WideExact.mul x y=.ok z ∧ CanonicalE z ∧ decodeE z=decodeE x*decodeE y := by
  obtain ⟨ac,hac,cac,vac⟩ := k_mul x.c0 y.c0 hx.1 hy.1
  obtain ⟨bd,hbd,cbd,vbd⟩ := k_mul x.c1 y.c1 hx.2 hy.2
  obtain ⟨a,ha,ca,va⟩ := k_add x.c0 x.c1 hx.1 hx.2
  obtain ⟨b,hb,cb,vb⟩ := k_add y.c0 y.c1 hy.1 hy.2
  obtain ⟨cross,hcross,ccross,vcross⟩ := k_mul a b ca cb
  obtain ⟨u,hu,cu,vu⟩ := k_mul_u bd cbd
  obtain ⟨lo,hlo,clo,vlo⟩ := k_add ac u cac cu
  obtain ⟨hi0,hhi0,chi0,vhi0⟩ := k_sub cross ac ccross cac
  obtain ⟨hi,hhi,chi,vhi⟩ := k_sub hi0 bd chi0 cbd
  refine ⟨⟨lo,hi⟩,?_,⟨clo,chi⟩,?_⟩
  · simp only [field.wide_exact.WideExact.mul,hac,hbd,ha,hb,hcross,hu,hlo,hhi0,hhi,bind_tc_ok]
  · apply QuadraticAlgebra.ext
    · change decodeK lo=(decodeE x*decodeE y).re
      rw [QuadraticAlgebra.re_mul]
      change decodeK lo=decodeK x.c0*decodeK y.c0+U*decodeK x.c1*decodeK y.c1
      rw [vlo,vac,vu,vbd]
      ring
    · change decodeK hi=(decodeE x*decodeE y).im
      rw [QuadraticAlgebra.im_mul]
      change decodeK hi=decodeK x.c0*decodeK y.c1+decodeK x.c1*decodeK y.c0+0*decodeK x.c1*decodeK y.c1
      rw [vhi,vhi0,vcross,va,vb,vac,vbd]
      ring

#print axioms mul
#print axioms m_sub_transport
#print axioms cm_sub_transport
#print axioms k_sub
#print axioms cm_r_transport
#print axioms cm_r_words
#print axioms k_mul_u
end AspisR1.CuSavingsWideArithmetic
