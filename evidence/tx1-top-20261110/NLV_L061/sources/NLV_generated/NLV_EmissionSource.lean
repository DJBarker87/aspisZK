import NLV_PairElim
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLV_EmissionSource
open Aeneas Aeneas.Std Result AspisR1CurrentCaller NLJ_Tx1
/-- Focused structural normalization: only named suffix definitions and the
pair eliminator are expanded. The earlier broad congruence shape is retired. -/
theorem source (cfg : Configuration) (i : Input) :
 NLV_Emitted.suffix_guard cfg i = GExp_FirstCode.code cfg.base cfg.boundaries cfg.std
 i.hashv i.digest i.publicValue i.publicBytes i.proof i.k := by
 simp only [NLV_Emitted.suffix_guard,NLV_Emitted.suffix_parse,NLV_Emitted.suffix_scan,NLV_Emitted.suffix_markParsed,NLV_Emitted.suffix_zero,NLV_Emitted.suffix_prepare,NLV_Emitted.suffix_accumulator,NLV_Emitted.suffix_markPrepare,NLV_Emitted.suffix_foldedSlice,NLV_Emitted.suffix_foldedCopy,NLV_Emitted.suffix_foldedUnwrap,NLV_Emitted.suffix_batch0,NLV_Emitted.suffix_markMerkle,NLV_Emitted.suffix_geometry,NLV_Emitted.suffix_pending,NLV_Emitted.suffix_query,NLV_Emitted.suffix_finishPending,NLV_Emitted.suffix_checkpoint,NLV_Emitted.suffix_markCheckpoint,NLV_Emitted.suffix_returned,
  GExp_FirstCode.code,NLV_Emitted.emittedTry,NLJ_Tx1.ops,NLV_PairElim.elim,Bind.bind,Pure.pure,NLV_Algebra.assoc,CheckpointBytes5Effect.bind]
 try rfl
#print axioms source
end AspisR1.NLV_EmissionSource
end
