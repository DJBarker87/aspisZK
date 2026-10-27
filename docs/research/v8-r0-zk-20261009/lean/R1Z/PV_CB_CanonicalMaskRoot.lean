import R1Z.PV_CB_CanonicalLinears
import R1Z.PV_CB_CanonicalFill
import R1Z.PV_CB_CanonicalHorner
import R1Z.PV_CB_CanonicalPower26
import R1Z.PV_CB_MaskRootEq
set_option autoImplicit false
namespace R1Z.PV_CB_CanonicalMaskRoot
open Aeneas Aeneas.Std Result ProverRwSuccessReverseRange PV_CB_ForwardRange
abbrev Q := PV_CB_CanonicalTower.Q
abbrev Valid := PV_CB_CanonicalTower.Valid
abbrev ValidArray {N : Usize} (a : Array Q N) := PV_CB_CanonicalArrays.Valid Valid a

/-- Numerical invariant of the retained source control. This does not bind the
    fresh shipped callback, and does not assume any desired returned value. -/
theorem source (c1 : Array Q 16#usize) (mask : Array Q 10#usize) (g : Q)
    (point : Array Q 10#usize) (vc1 : ValidArray c1) (vmask : ValidArray mask)
    (vg : Valid g) (vpoint : ValidArray point) :
    ∃ out, PV_CB_MaskSource.state_only_hiding.state_only_selected_mask_value c1 mask g point = ok out ∧ Valid out := by
  obtain ⟨linear,explicitLinear,hlinear,vlinear,vexplicit⟩ := PV_CB_CanonicalLinears.source point vpoint
  let initial := Array.repeat 27#usize ProverRwP7CurrentFieldSource.aspis_core.field.QM31.ZERO
  have vinitial : ValidArray initial := PV_CB_CanonicalArrays.repeat_valid Valid 27#usize _ PV_CB_CanonicalConstants.zero
  obtain ⟨coeff1,hcoeff1,vcoeff1⟩ := PV_CB_CanonicalFill.c1 c1 initial vc1 vinitial
  obtain ⟨coeff2,hcoeff2,vcoeff2⟩ := PV_CB_CanonicalFill.mask mask coeff1 vmask vcoeff1
  obtain ⟨prepared,hprepared,vprepared⟩ := PV_CB_CanonicalPreparedCtor.new linear vlinear
  obtain ⟨shared,hshared,vshared⟩ := PV_CB_CanonicalArrays.read Valid coeff2 vcoeff2 26#usize (by decide)
  obtain ⟨horner,hhorner,vhorner⟩ := PV_CB_CanonicalHorner.source coeff2 prepared 26#usize shared (by decide) vcoeff2 vprepared vshared
  obtain ⟨power,hpower,vpower⟩ := PV_CB_CanonicalPower26.power26 explicitLinear vexplicit
  obtain ⟨factor,hfactor,vfactor⟩ := PV_CB_CanonicalQuartic.add _ power PV_CB_CanonicalConstants.one vpower
  obtain ⟨product,hproduct,vproduct⟩ := PV_CB_CanonicalQuartic.mul factor g vfactor vg
  obtain ⟨out,hout,vout⟩ := PV_CB_CanonicalQuartic.add horner product vhorner vproduct
  refine ⟨out,?_,vout⟩
  simp only [between,PV_CB_MaskHorner.S.loop,before,PV_CB_PreparedTotal.S.new,
    PV_CB_CurrentQuartic.S.add,PV_CB_CurrentQuartic.S.mul] at hcoeff1 hcoeff2 hprepared hhorner hfactor hproduct hout
  simp only [PV_CB_MaskSource.state_only_hiding.state_only_selected_mask_value,
    PV_CB_MaskSource.state_only_hiding.STATE_ONLY_HIDING_C1_COLUMNS,
    PV_CB_MaskSource.state_only_hiding.STATE_ONLY_HIDING_MASK_ONLY_C1_COLUMNS,
    PV_CB_MaskSource.state_only_hiding.STATE_ONLY_HIDING_FACTOR_DEGREE,
    core.iter.traits.iterator.Iterator.rev.default,
    core.iter.traits.iterator.Iterator.rev.trait_default,
    hlinear,bind_tc_ok]
  change (do
    let c1' ← PV_CB_MaskSource.state_only_hiding.state_only_selected_mask_value_loop0
      {start := 0#usize, «end» := 16#usize} c1 initial
    let c2' ← PV_CB_MaskSource.state_only_hiding.state_only_selected_mask_value_loop1
      {start := 0#usize, «end» := 10#usize} mask c1'
    let prepared' ← ProverRwP7CurrentFieldSource.aspis_core.field.PreparedQm31Multiplier.new linear
    let shared' ← Array.index_usize c2' 26#usize
    let horner' ← PV_CB_MaskSource.state_only_hiding.state_only_selected_mask_value_loop2
      {iter := {start := 0#usize, «end» := 26#usize}} c2' prepared' shared'
    let power' ← PV_CB_MaskSource.state_only_hiding.mask_power_26 explicitLinear
    let factor' ← ProverRwP7CurrentFieldSource.aspis_core.field.QM31.add
      ProverRwP7CurrentFieldSource.aspis_core.field.QM31.ONE power'
    let product' ← ProverRwP7CurrentFieldSource.aspis_core.field.QM31.mul factor' g
    ProverRwP7CurrentFieldSource.aspis_core.field.QM31.add horner' product') = ok out
  simp only [hcoeff1,hcoeff2,hprepared,hshared,hhorner,hpower,hfactor,hproduct,hout,bind_tc_ok]

theorem owned (c1 : Array Q 16#usize) (mask : Array Q 10#usize) (g : Q)
    (point : Array Q 10#usize) (vc1 : ValidArray c1) (vmask : ValidArray mask)
    (vg : Valid g) (vpoint : ValidArray point) :
    ∃ out, PV_CB_OwnedMask.owned.mask c1 mask g point = ok out ∧ Valid out := by
  obtain ⟨out,hout,vout⟩ := source c1 mask g point vc1 vmask vg vpoint
  exact ⟨out,(PV_CB_MaskRootEq.reference c1 mask g point).trans hout,vout⟩
#print axioms source
#print axioms owned
end R1Z.PV_CB_CanonicalMaskRoot
