import PoolT_Snapshot
set_option autoImplicit false
noncomputable section
namespace AspisR1.PoolT_Child
open Aeneas Aeneas.Std Result S2W_D189Entry

/-- No mapped error can produce a successful verifier checkpoint. The called
verifier gets the actual semantic/public/proof/split arguments and None. -/
theorem decoded (ops : AdapterRw.Ops)
    (semantic : AdapterRw.aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (public proof : Slice U8) (split : Usize) (saved : alloc.vec.Vec U8)
    (accepted : AdapterRw.first_decoded ops semantic public proof split = ok (.Ok saved)) :
    ops.op10 (AdapterRw.SolanaDigest.Insts.Aspis_coreDigestDigest32 ops)
      semantic public proof split () none = ok (.Ok saved) := by
  rw [AdapterRw.Cuts.first_decoded_call] at accepted
  obtain ⟨reply,called,rest⟩ := AdapterRw.Cuts.bind_success _ _ _ accepted
  cases reply with
  | Ok value =>
    have same : value = saved := by
      simpa [AdapterRw.core.result.Result.map_err] using rest
    subst value
    exact called
  | Err error =>
    simp only [AdapterRw.core.result.Result.map_err] at rest
    exact False.elim (AdapterRw.Cuts.error_bind_ne_ok _ _ rest)

/-- Full native owned-call inversion, retaining fixed original buffer values,
strict statement decoder, semantic getter, selected proof and actual child.
No independently selected successful native child is supplied. -/
theorem original_inputs (ops : AdapterRw.Ops) (e : Entry)
    (program : S2W_ExtractionBoundary.Program) (data : Slice U8) (saved : alloc.vec.Vec U8)
    (accepted : AdapterRw.r1_pool_adapter.owned.stage1_owned ops program e.first data = ok (.Ok saved)) :
    ∃ statement semantic proof split,
      ops.op47 (e.buffers (e.handles 1).1) = ok (.Ok statement) ∧
      AdapterRw.aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1.semantic_public
        statement = ok semantic ∧
      core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
        (e.buffers (e.handles 0).1) {start := 688#usize, «end» := 58295#usize} = ok proof ∧
      ops.op10 (AdapterRw.SolanaDigest.Insts.Aspis_coreDigestDigest32 ops)
        semantic (e.buffers (e.handles 1).1) proof split () none = ok (.Ok saved) := by
  obtain ⟨pa,pu,pub,raw,statement,semantic,proof,split,ipa,ipu,rpa,rpu,decode,getter,range,child,_⟩ :=
    AdapterRw.Accepted.first_call ops program e.first data saved accepted
  have at0 := Result.ok.inj (ipa.symm.trans (first_index e).1)
  have at1 := Result.ok.inj (ipu.symm.trans (first_index e).2.1)
  subst pa; subst pu
  have rawSame := (PoolT_Snapshot.data ops e 0 58295 58295 raw rpa).1
  have pubSame := (PoolT_Snapshot.data ops e 1 1880 1880 pub rpu).1
  subst raw; subst pub
  exact ⟨statement,semantic,proof,split,decode,getter,range,
    decoded ops semantic _ proof split saved child⟩

#print axioms decoded
#print axioms original_inputs
end AspisR1.PoolT_Child
end
