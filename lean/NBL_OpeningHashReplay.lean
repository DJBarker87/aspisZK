import NBL_EffectControl
import NBL_ScalarHashReplay
import NBL_OpeningTrace
import NBL_CohortCode
set_option autoImplicit false
namespace AspisR1.NBL_OpeningHashReplay
open Aeneas Aeneas.Std Result AspisR1PublicPreparation PreparedHashCode NBL_CodeRunLaws

/-- Exact ordered typed hash log AND the sole opening carrier, replayed in the
existing preparation effect tree. No independently supplied opening result. -/
theorem source {H : Type} (D : aspis_core.Digest32 H)
    (sem : r1_semantic.Verified H) (v : verifier.View) (hash : H)
    (t : NBL_OpeningTrace.Trace D sem v hash) :
    run (NBL_EffectControl.opening
      (preparationEffects NBA_Installed.actual NBL_QueryDictionary.boundaries) D sem v hash)=
      (NBL_HashReplay.events D hash t.log,ok t.output) := by
  have seeded := NBL_HashReplay.seed D hash sem.transcript.state t.seed t.seedCall
  have gamma := NBL_ScalarHashReplay.scalar D (⟨t.seed,hash⟩ : transcript.Transcript H) 27#u8 v.y1 true t.gamma
  have kappa := NBL_ScalarHashReplay.scalar D t.gamma.block.after 28#u8 (Array.to_slice t.inactiveBytes) false t.kappa
  have alpha0 := NBL_ScalarHashReplay.scalar D t.kappa.block.after 29#u8 v.round0 false t.alpha0
  have alpha1 := NBL_ScalarHashReplay.scalar D t.alpha0.block.after 30#u8 (alloc.vec.Vec.deref t.bytes2) false t.alpha1
  have folds : transport.Variant.folds v.variant=ok 2#usize := by
    rw [t.variant]
    simp [transport.Variant.folds,transport.Variant.Insts.CoreCmpPartialEqVariant.eq,transport.Variant.read_discriminant]
  have capacity : (32#usize+224#usize : Result Usize)=ok 256#usize := by
    obtain ⟨x,call,value⟩ := WP.spec_imp_exists
      (UScalar.add_spec (x:=32#usize) (y:=224#usize) (by scalar_tac))
    have same : x=256#usize := by scalar_tac
    simpa only [same] using call
  have root : core.option.Option.unwrap v.folded_root=ok t.root := by rw [t.rootCall];rfl
  simp only [NBL_BlockTrace.Block.after] at gamma kappa alpha0 alpha1
  rw [t.variant] at folds
  simp only [NBL_EffectControl.opening,preparationEffects,
    r1_wire.SemanticTranscript.impl.state,bind_run,lift_run,pure_run,chain,
    t.variant,seeded,gamma,kappa,alpha0,alpha1,t.serialize,folds,capacity,root,
    t.appendRoot,t.appendRound,lift,Aeneas.Std.uncurry,↓reduceIte,
    NBL_OpeningTrace.Trace.output,NBL_OpeningTrace.Trace.log,NBL_HashReplay.events,
    NBL_BlockTrace.Block.after,List.map_append,List.map_cons,List.map_nil,
    List.nil_append,List.append_nil,List.append_assoc]

#print axioms source
end AspisR1.NBL_OpeningHashReplay
