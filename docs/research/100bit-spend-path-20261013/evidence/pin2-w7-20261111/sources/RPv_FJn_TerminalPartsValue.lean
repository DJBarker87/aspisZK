import RPv_FJn_CompositionCopyOnRun
import RPv_FIr_RootRefined
set_option autoImplicit false
/-! PIN2 W11 (2026-11-11): the model side (`ofPublic`) takes the PIN2 `PIN2P.SemanticPublic`
(W3c), so the public binder is now `FIw_PublicModel.Public` instead of the pre-PIN2 native
`SemPub`; every pre-PIN2 native read (`composition`, `FIr_TerminalTrace.parts`, the native
`Bounds`, and the host-built native lemmas) takes its projection `.dropDestination`, as in W3c's
OnRun modules.  Field reads `.variant` / `.transition` are the same fields (rfl).  See CHANGES.tsv
for which conjuncts changed text. -/
noncomputable section
namespace AspisR1.FJn_TerminalPartsValue
open Aeneas Aeneas.Std Result FIq_Native
open FIv_NativeValue (K Canon decode)
open FIw_ArrayValue (canonical decoded)
open FIw_CompositionOrigins (SemPub composition)
open FIz_ConcretePack (embed)
/-- All native terminal-parts arithmetic, using the complete copy seed of the
same composition call. Canonicality of composition outputs is derived. -/
theorem value (pub : FIw_PublicModel.Public) (claims : Array field.QM31 84#usize)
    (point zc : Array field.QM31 10#usize) (lambda chi theta mu out : field.QM31)
    (c1 : Array field.QM31 16#usize) (mask : Array field.QM31 10#usize) (g : field.QM31)
    (hc : canonical claims) (hp : canonical point) (hz : canonical zc)
    (hlambda : Canon lambda) (hchi : Canon chi) (htheta : Canon theta) (hmu : Canon mu)
    (bounds : FJa_PublicBounds.Bounds pub.dropDestination)
    (run : FIr_TerminalTrace.parts pub.dropDestination claims point lambda chi theta zc mu=ok (.Ok (out,c1,mask,g))) :
    ∃ (comp h active : field.QM31) (a a1 a2 : Array field.QM31 16#usize)
      (s : pool_v1.pair_forest_copy_terminal.Selectors)
      (v : pool_v1.pair_forest_copy_terminal.PoolV1PairForestCompiledVariantV1),
      composition pub.dropDestination claims point lambda chi theta=ok (.Ok (comp,c1,mask,g,h,active)) ∧
      c1=a ∧ Canon out ∧
      decode out=FIr_TerminalValue.formula
        (R0P.SemSource.eqValue (fun j=>FIv_NativeArray.value zc j.val)
          (fun j=>FIv_NativeArray.value point j.val))
        (decode comp) (decode mu) (decode h) (decode active) ∧
      decode active=(FJn_CompositionCopyOnRun.copyModel a h s lambda chi
        pub.transition.live_snapshot.next_pair_index v).2 ∧
      embed (decode comp)=ExtractedMaskTerminalHorner.composeGroups (embed (decode theta))
        (embed (FJn_CompositionCopyOnRun.copyModel a h s lambda chi
          pub.transition.live_snapshot.next_pair_index v).1)
        (FJk_CompositionWideOnRun.semantic pub ⟨a,a1,a2⟩ s)
        (FJk_CompositionWideOnRun.poseidon pub ⟨a,a1,a2⟩ s) := by
  obtain ⟨comp,h,active,called,hh,finish⟩ :=
    FIr_RootRefined.parts pub.dropDestination claims point zc lambda chi theta mu out c1 mask g run hc hz hp hmu
  obtain ⟨a,a1,a2,s,v,same,_,_,cc,ca,av,cv⟩ :=
    FJn_CompositionCopyOnRun.value pub claims point lambda chi theta comp g h active c1 mask
      hc hp hlambda hchi htheta bounds called
  have got:=finish cc ca
  exact ⟨comp,h,active,a,a1,a2,s,v,called,same,got.1,got.2,av,cv⟩
#print axioms value
end AspisR1.FJn_TerminalPartsValue
end
