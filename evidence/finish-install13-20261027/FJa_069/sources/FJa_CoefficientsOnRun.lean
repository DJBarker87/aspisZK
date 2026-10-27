import FIz_SameComposition
import FJa_BoxedMass
import FJa_PublicBounds
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJa_CoefficientsOnRun
open Aeneas Aeneas.Std Result FIq_Native
open FIv_NativeArithmetic (NQ)
open FIv_NativeValue (K)
open FIw_ArrayValue (canonical decoded)
open FIw_ScalarSuffix (Public Openings Selectors)
/-- FIz's SAME composition call, now WITHOUT boxed selector canonicality or
mass premises: the original reader point/constructor derives all four. -/
theorem value (p : Public) (claims : Array NQ 84#usize) (point : Array NQ 10#usize)
    (lambda chi theta comp g h active : NQ) (c1 : Array NQ 16#usize) (mask : Array NQ 10#usize)
    (hclaims : canonical claims) (hpoint : canonical point) (hb : FJa_PublicBounds.Bounds p)
    (success : pool_v1.pair_forest_semantic_terminal.composition_parts p claims point lambda chi theta=
      ok (.Ok (comp,c1,mask,g,h,active))) :
    ∃ (a a1 a2 : Array NQ 16#usize) (s : Selectors) (semantic : Array NQ 24#usize),
      c1=a ∧ canonical a ∧ canonical a1 ∧ canonical a2 ∧
      pool_v1.pair_forest_copy_terminal.Selectors.boxed_at_point point=ok s ∧
      pool_v1.pair_forest_semantic_terminal.semantic_packed p ⟨a,a1,a2⟩ s=ok semantic ∧
      canonical s.high ∧ canonical s.low ∧
      (∑ h : Fin 64,FIv_NativeArray.value s.high h.val)=1 ∧
      (∑ l : Fin 16,FIv_NativeArray.value s.low l.val)=1 ∧
      canonical semantic ∧ decoded semantic=fun j=>FIx_PreweightedPack.pack
        (fun i=>R0P.SemSource.scalarLaneAt (FIw_PublicModel.ofPublic p)
          (FIw_PublicModel.openings ⟨a,a1,a2⟩) (FIw_PublicModel.selector s) (4*j.val+i.val)) := by
  obtain ⟨ha,hn,hc,hr,hf,hnr,hnf,hab,haw⟩ := hb
  obtain ⟨a,a1,a2,s,semantic,same,ca,ca1,ca2,hs,hsem,v⟩ :=
    FIz_SameComposition.on_run p claims point lambda chi theta comp g h active c1 mask
      hclaims ha hn hr hc hf hnr hnf hab haw success
  have canon := FJa_BoxedCanonical.value point s hpoint hs
  have mass := FJa_BoxedMass.value point s hpoint hs
  have result := v canon.1 canon.2 mass.1 mass.2
  exact ⟨a,a1,a2,s,semantic,same,ca,ca1,ca2,hs,hsem,canon.1,canon.2,mass.1,mass.2,result⟩
#print axioms value
end AspisR1.FJa_CoefficientsOnRun
end
