import RPu_FJk_HornerValue
import RPu_FJk_CopyCanonical
import RPu_FJk_Native07Value
import RPu_FIz_WideCoefficientsOnRun
import RPu_FJa_PublicBounds
import RPu_FIr_H1Canonical
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJk_CompositionValue
open Aeneas Aeneas.Std Result FIq_Native
open FIv_NativeValue (K Canon decode)
open FIw_ArrayValue (canonical decoded)
open FIw_CompositionOrigins (SemPub composition)
/-- Complete composition arithmetic VALUE on ONE origin cut; copy's remaining
model identification is separate. No child output canonicality is assumed. -/
theorem value (pub : SemPub) (claims : Array field.QM31 84#usize) (point : Array field.QM31 10#usize)
    (lambda chi theta comp g h active : field.QM31)
    (c1 : Array field.QM31 16#usize) (mask : Array field.QM31 10#usize)
    (hclaims : canonical claims) (hpoint : canonical point)
    (hlambda : Canon lambda) (hchi : Canon chi) (htheta : Canon theta)
    (bounds : FJa_PublicBounds.Bounds pub)
    (run : composition pub claims point lambda chi theta=ok (.Ok (comp,c1,mask,g,h,active))) :
    ∃ (a a1 a2 : Array field.QM31 16#usize)
      (s : pool_v1.pair_forest_copy_terminal.Selectors)
      (po : state_only_poseidon.StateOnlyPoseidonSelectors)
      (semantic : Array field.QM31 24#usize) (poseidon : Array field.QM31 4#usize)
      (copy : pool_v1.pair_forest_copy_terminal.PoolV1PairForestCompiledCopyTerminalV1),
      c1=a ∧ pool_v1.pair_forest_copy_terminal.Selectors.boxed_at_point point=ok s ∧
      pool_v1.pair_forest_semantic_terminal.poseidon_selectors s=ok po ∧
      pool_v1.pair_forest_semantic_terminal.semantic_packed pub ⟨a,a1,a2⟩ s=ok semantic ∧
      state_only_poseidon.evaluate_state_only_poseidon_oracle_projected ⟨a,a1,a2⟩ po=ok poseidon ∧
      canonical semantic ∧ canonical poseidon ∧ Canon copy.residual ∧ Canon active ∧ Canon comp ∧
      decoded semantic=FIy_NativeCoefficients.model pub ⟨a,a1,a2⟩ s ∧
      (decoded poseidon=fun group=>R0P.poseidonPackingFormula
        ExtractedMaskQmPackBase4Arithmetic.iBasis ExtractedMaskQmPackBase4Arithmetic.uBasis
        (fun j=>R0P.poseidonScalarResidual (FJh_Native07RawValue.openings ⟨a,a1,a2⟩)
          (decode po.block) (decoded po.local) (FJe_ExternalAdjoint.lane group j))) ∧
      decode comp=FIv_CompositionValue.polynomial (decode theta) semantic poseidon copy.residual := by
  obtain ⟨a,a1,a2,s,po,variant,semantic,poseidon,prepared,middle,copy,it,it1,
    same,r0,r1,r2,rs,rsp,rpo,rsem,rv,rc,rp,rit,rit1,rm,rf,ra⟩ :=
    FIw_CompositionOrigins.reached pub claims point lambda chi theta comp g h active c1 mask run
  have ca := FIw_OpeningCanonical.z claims a hclaims r0
  have ca1 := FIw_OpeningCanonical.succ claims a1 hclaims r1
  have ca2 := FIw_OpeningCanonical.xor12 claims a2 hclaims r2
  have cs := FJa_BoxedCanonical.value point s hpoint rs
  have ps := FJa_PoseidonSelectors.value s po cs.1 cs.2 rsp
  have pos := FJk_Native07Value.value ⟨a,a1,a2⟩ po poseidon ca ca1 ca2 ps.2.1 ps.2.2.1 rpo
  obtain ⟨ha,hn,hchange,hr,hf,hnr,hnf,hab,haw⟩ := bounds
  have sem := FIy_NativeCoefficients.value pub ⟨a,a1,a2⟩ s semantic ca ca1 ca2 cs.1 cs.2
    ha hn hr hchange hf hnr hnf hab haw rsem
  have hh := FIr_H1Canonical.canonical pub claims point lambda chi theta comp g h active c1 mask run hclaims
  have cp := FJk_CopyCanonical.value a h s lambda chi pub.transition.live_snapshot.next_pair_index variant copy
    ca hh cs.1 cs.2 hlambda hchi rc
  have cv := FJk_HornerValue.value semantic poseidon prepared theta copy.residual middle comp it it1
    htheta cp.1 sem.1 pos.1 rp rit rit1 rm rf
  exact ⟨a,a1,a2,s,po,semantic,poseidon,copy,same,rs,rsp,rsem,rpo,sem.1,pos.1,cp.1,
    ra ▸ cp.2,cv.1,sem.2,pos.2,cv.2⟩
#print axioms value
end AspisR1.FJk_CompositionValue
end
