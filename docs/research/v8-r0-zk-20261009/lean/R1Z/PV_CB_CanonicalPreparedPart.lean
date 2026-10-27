import R1Z.PV_CB_CanonicalPreparedCtor
set_option autoImplicit false
namespace R1Z.PV_CB_CanonicalPreparedPart
open Aeneas Aeneas.Std Result PV_CB_CanonicalPreparedCtor

theorem mul_part (left : Part) (right : C) (hl : PartValid left)
    (hr : PV_CB_CanonicalComplex.Valid right) :
    ∃ out, PV_CB_PreparedTotal.S.mulPart () (left,right) = ok out ∧
      PV_CB_CanonicalComplex.Valid out := by
  obtain ⟨a,ha,va⟩ := PV_CB_CanonicalArrays.read PV_CB_CanonicalM31.Valid left hl 0#usize (by decide)
  obtain ⟨b,hb,vb⟩ := PV_CB_CanonicalArrays.read PV_CB_CanonicalM31.Valid left hl 1#usize (by decide)
  obtain ⟨s,hs,vs⟩ := PV_CB_CanonicalArrays.read PV_CB_CanonicalM31.Valid left hl 2#usize (by decide)
  obtain ⟨ac,hac,vac⟩ := PV_CB_CanonicalM31.mul a right.a
  obtain ⟨bd,hbd,vbd⟩ := PV_CB_CanonicalM31.mul b right.b
  obtain ⟨sum,hsum,vsum⟩ := PV_CB_CanonicalM31Ops.add right.a right.b hr.1 hr.2
  obtain ⟨product,hproduct,vproduct⟩ := PV_CB_CanonicalM31.mul s sum
  obtain ⟨real,hreal,vreal⟩ := PV_CB_CanonicalM31Ops.sub ac bd vac vbd
  obtain ⟨cross,hcross,vcross⟩ := PV_CB_CanonicalM31Ops.sub product ac vproduct vac
  obtain ⟨imaginary,himaginary,vimaginary⟩ := PV_CB_CanonicalM31Ops.sub cross bd vcross vbd
  refine ⟨⟨real,imaginary⟩,?_,⟨vreal,vimaginary⟩⟩
  change (do
    let a ← Array.index_usize left 0#usize
    let ac ← ProverRwP7CurrentBaseBridge.S.mul a right.a
    let b ← Array.index_usize left 1#usize
    let bd ← ProverRwP7CurrentBaseBridge.S.mul b right.b
    let s ← Array.index_usize left 2#usize
    let sum ← ProverRwP7CurrentBaseBridge.S.add right.a right.b
    let product ← ProverRwP7CurrentBaseBridge.S.mul s sum
    let real ← ProverRwP7CurrentBaseBridge.S.sub ac bd
    let cross ← ProverRwP7CurrentBaseBridge.S.sub product ac
    let imaginary ← ProverRwP7CurrentBaseBridge.S.sub cross bd
    ok ({a := real,b := imaginary} : C)) = ok _
  rw [ha]
  simp only [bind_tc_ok]
  rw [hac]
  simp only [bind_tc_ok]
  rw [hb]
  simp only [bind_tc_ok]
  rw [hbd]
  simp only [bind_tc_ok]
  rw [hs]
  simp only [bind_tc_ok]
  rw [hsum]
  simp only [bind_tc_ok]
  rw [hproduct]
  simp only [bind_tc_ok]
  rw [hreal]
  simp only [bind_tc_ok]
  rw [hcross]
  simp only [bind_tc_ok]
  rw [himaginary]
  simp only [bind_tc_ok]
#print axioms mul_part
end R1Z.PV_CB_CanonicalPreparedPart
