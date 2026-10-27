import FJa_CoefficientsOnRun
import FJa_BoxedSelAt
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJa_SemanticPoint
open Aeneas Aeneas.Std Result FIq_Native
open FIv_NativeArithmetic (NQ)
open FIw_ArrayValue (canonical decoded)
open FIw_ScalarSuffix (Public Openings Selectors)
/-- ALL24 native semantic values at the literal SAME decoded reader point.
FIz arithmetic is imported unchanged; selector bounds/mass/meaning are derived. -/
theorem value (p : Public) (claims : Array NQ 84#usize) (point : Array NQ 10#usize)
    (lambda chi theta comp g h active : NQ) (c1 : Array NQ 16#usize) (mask : Array NQ 10#usize)
    (hclaims : canonical claims) (hpoint : canonical point) (hb : FJa_PublicBounds.Bounds p)
    (success : pool_v1.pair_forest_semantic_terminal.composition_parts p claims point lambda chi theta=
      ok (.Ok (comp,c1,mask,g,h,active))) :
    ∃ (a a1 a2 : Array NQ 16#usize) (s : Selectors) (semantic : Array NQ 24#usize),
      c1=a ∧ canonical a ∧ canonical a1 ∧ canonical a2 ∧
      pool_v1.pair_forest_copy_terminal.Selectors.boxed_at_point point=ok s ∧
      pool_v1.pair_forest_semantic_terminal.semantic_packed p ⟨a,a1,a2⟩ s=ok semantic ∧
      canonical semantic ∧ decoded semantic=fun j=>FIx_PreweightedPack.pack
        (fun i=>R0P.SemSource.scalarLaneAt (FIw_PublicModel.ofPublic p)
          (FIw_PublicModel.openings ⟨a,a1,a2⟩) (R0P.SemSource.selAt (decoded point)) (4*j.val+i.val)) := by
  obtain ⟨a,a1,a2,s,semantic,same,ca,ca1,ca2,hs,hsem,_,_,_,_,csem,v⟩ :=
    FJa_CoefficientsOnRun.value p claims point lambda chi theta comp g h active c1 mask hclaims hpoint hb success
  rw [FJa_BoxedSelAt.value point s hpoint hs] at v
  exact ⟨a,a1,a2,s,semantic,same,ca,ca1,ca2,hs,hsem,csem,v⟩
#print axioms value
end AspisR1.FJa_SemanticPoint
end
