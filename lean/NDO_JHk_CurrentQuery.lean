import NDO_JHc_InstalledQuery
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHk_CurrentQuery
open Aeneas Aeneas.Std Result AspisR1CurrentCaller JGr_Geometry

/-- Installation equality is checked with an abstract seed, before using
the large concrete fixture dictionary. -/
theorem dictionary (seed : Port3_NativeQueryBody.Ops) :
    Tx1Q_QueryBridge.leaves (SAQ_Decoder.install (JFr_TX2_DotsBinding.ops seed))=
      JGc_TX2_QueryDictionary.ops seed := by
  rfl
#print axioms dictionary

theorem source (p : verifier.Prepared) (initial out : verifier.Accumulator)
    (scratch : Array aspis_core.field.wide_exact.WideExact 29#usize)
    (g : verifier.QueryGeometry) (pending after : verifier.BatchedWeights)
    (query : installed.op7 JFx_NativeBytes.proof p initial scratch none g pending 10#usize=
      ok (.Ok (out,after))) :
    Port3_NativeQueryBody.verifier.candidate.query_loop JHa_QueryLoop.ops
      JFx_NativeBytes.proof (Tx1Q_Carriers.prepared p) (Tx1Q_Carriers.accumulator initial)
      (Tx1Q_Carriers.arr Tx1Q_Carriers.e scratch) none (Tx1Q_Carriers.geometry g)
      (Tx1Q_Carriers.pending pending) 10#usize=
        ok (.Ok (Tx1Q_Carriers.accumulator out,Tx1Q_Carriers.pending after)) := by
  rw [JGw_InstalledSlots.query] at query
  have native := Tx1Q_Install.query_success
    (Tx1Q_QueryBridge.leaves (SAQ_Decoder.install (JFr_TX2_DotsBinding.ops JGp_Seeds.query)))
    JFx_NativeBytes.proof p initial out scratch none g pending after 10#usize query
  rw [Tx1Q_QueryBridge.release_leaves,dictionary] at native
  exact native
#print axioms source
end AspisR1.JHk_CurrentQuery
end
