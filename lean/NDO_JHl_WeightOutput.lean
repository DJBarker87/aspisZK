import NDO_JHl_AllWeightCells
import NDO_JHl_ByteBlocks
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHl_WeightOutput
open Aeneas Aeneas.Std Result AspisR1CurrentCaller
open InstalledPreparation FirstComposition JGr_Geometry JHe_CurrentWriterImage

theorem mapped (xs : List aspis_core.field.QM31) :
    (((xs.map Tx1Q_Carriers.k).map CheckpointBytes3Namespaces.toK).flatMap WAdm_SourceBody.putK).map
      CheckpointBytes5Writer.u8=xs.flatMap JHl_WeightCell.encoded := by
  induction xs with
  | nil => rfl
  | cons q xs ih =>
    simp only [List.map_cons,List.flatMap_cons,List.map_append,ih]
    rfl
#print axioms mapped

theorem pack (xs : List aspis_core.field.QM31) (size : xs.length=64)
    (cells : ∀ j : Fin 64,∃ q,xs[j.val]?=some q ∧
      CheckpointBytes5Output.ofK (Tx1Q_Carriers.k q)=JHl_WeightFormula.totalAt 10 j.val ∧
      Port3_FlushInstall.Canonical (Tx1Q_Carriers.k q)) :
    xs.flatMap JHl_WeightCell.encoded=(JFx_NativeBytes.checkpoint.val.drop 712).take 1024 := by
  have selected : ∀ j : Fin 64,
      JHl_WeightCell.encoded (xs[j.val]'(by rw [size];exact j.isLt))=
        (JFx_NativeBytes.checkpoint.val.drop (712+16*j.val)).take 16 := by
    intro j
    obtain ⟨q,read,meaning,canonical⟩ := cells j
    have same : xs[j.val]'(by rw [size];exact j.isLt)=q := by
      have h := List.getElem?_eq_getElem (l:=xs) (by rw [size];exact j.isLt)
      exact Option.some.inj (h.symm.trans read)
    rw [same]
    exact JHl_AllWeightCells.source j q canonical meaning
  rw [←WAdm_SourceBody.ofFn_array xs size,WAdm_SourceBody.flatMap_ofFn]
  have h : (fun j : Fin 64 => JHl_WeightCell.encoded (xs[j.val]'(by rw [size];exact j.isLt)))=
      (fun j : Fin 64 => (JFx_NativeBytes.checkpoint.val.drop (712+16*j.val)).take 16) := funext selected
  rw [h]
  exact JHl_ByteBlocks.blocks JFx_NativeBytes.checkpoint.val 712 16 64
#print axioms pack

theorem source (p : verifier.Prepared)
    (input scratch : Array aspis_core.field.wide_exact.WideExact 29#usize)
    (initial out : verifier.Accumulator) (pending after : verifier.BatchedWeights)
    (g : verifier.QueryGeometry) (flushed : Slice aspis_core.field.QM31)
    (prepare : verifier.candidate.prepare installed digest (toCurrentPublic JFs_PublicSerialization.value)
      JFx_NativeBytes.proof () none input=ok (.Ok p,scratch))
    (init : installed.op20 .S2=ok (.Ok initial))
    (pend : installed.op18 initial.weights.deref=ok (.Ok pending))
    (geo : installed.op19 p.queries 0#usize 10#usize=ok (.Ok g))
    (query : installed.op7 JFx_NativeBytes.proof p initial scratch none g pending 10#usize=
      ok (.Ok (out,after))) (flush : installed.op17 after out.weights.deref=ok flushed) :
    ((accumulator {out with weights:=⟨flushed.val,flushed.property⟩}).weights.val.flatMap
      WAdm_SourceBody.putK).map CheckpointBytes5Writer.u8=
        (JFx_NativeBytes.checkpoint.val.drop 712).take 1024 := by
  have queries := JGp_CurrentQueries.source _ _ _ JGn_TerminalIdentified.shaDictionary () p input scratch prepare
  have cells := JHl_CurrentWeights.source p input scratch initial out pending after g flushed
    prepare queries init pend geo query flush
  obtain ⟨out1,after1,flushed1,run,finish,next,size,rest⟩ :=
    JHc_QueryPost.source p input scratch initial pending g prepare queries init pend geo
  have eq := core.result.Result.Ok.inj (Result.ok.inj (run.symm.trans query))
  have ea : out1=out := congrArg Prod.fst eq
  have eb : after1=after := congrArg Prod.snd eq
  subst out1 after1
  have ef : flushed1=flushed := Result.ok.inj (finish.symm.trans flush)
  subst flushed1
  change (((flushed.val.map Tx1Q_Carriers.k).map CheckpointBytes3Namespaces.toK).flatMap
    WAdm_SourceBody.putK).map _=_
  rw [mapped]
  exact pack flushed.val size cells
#print axioms source
end AspisR1.JHl_WeightOutput
end
