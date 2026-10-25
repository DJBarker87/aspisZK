import WAdm_EmittedScalars
import WAdm_Fold
set_option autoImplicit false
noncomputable section
open Aeneas Aeneas.Std Result ControlFlow
namespace AspisR1.WAdm_LoopShapes
open WAdm_Fissioned WAdm_model

theorem roots (xs : Array (Array U8 32#usize) 2#usize) (out : alloc.vec.Vec U8) :
    WAdm_roots out xs = WAdm_Fold.run WAdm_EmittedScalars.putDigest xs.val out := by
  simp only [WAdm_roots,WAdm_Fissioned.Array.Insts.CoreIterTraitsCollectIntoIteratorTIntoIter.into_iter,bind_tc_ok]
  unfold WAdm_roots_loop WAdm_Fold.run
  apply congrArg (fun body => loop body (xs.val,out))
  funext state
  rcases state with ⟨ys,v⟩
  cases ys <;> rfl

#print axioms roots

theorem early (xs : Array (WAdm_EmittedScalars.E) 4#usize) (out : alloc.vec.Vec U8) :
    WAdm_early out xs = WAdm_Fold.run WAdm_EmittedScalars.putE xs.val out := by
  simp only [WAdm_early,WAdm_Fissioned.Array.Insts.CoreIterTraitsCollectIntoIteratorTIntoIter.into_iter,bind_tc_ok]
  unfold WAdm_early_loop WAdm_Fold.run
  apply congrArg (fun body => loop body (xs.val,out))
  funext state
  rcases state with ⟨ys,v⟩
  cases ys <;> rfl

#print axioms early

theorem tail (xs : Array (WAdm_EmittedScalars.E) 2#usize) (out : alloc.vec.Vec U8) :
    WAdm_tail out xs = WAdm_Fold.run WAdm_EmittedScalars.putE xs.val out := by
  simp only [WAdm_tail,WAdm_Fissioned.Array.Insts.CoreIterTraitsCollectIntoIteratorTIntoIter.into_iter,bind_tc_ok]
  unfold WAdm_tail_loop WAdm_Fold.run
  apply congrArg (fun body => loop body (xs.val,out))
  funext state
  rcases state with ⟨ys,v⟩
  cases ys <;> rfl

#print axioms tail

theorem queries (xs : Array (U32) 22#usize) (out : alloc.vec.Vec U8) :
    WAdm_queries out xs = WAdm_Fold.run WAdm_EmittedScalars.putWord xs.val out := by
  simp only [WAdm_queries,WAdm_Fissioned.Array.Insts.CoreIterTraitsCollectIntoIteratorTIntoIter.into_iter,bind_tc_ok]
  unfold WAdm_queries_loop WAdm_Fold.run
  apply congrArg (fun body => loop body (xs.val,out))
  funext state
  rcases state with ⟨ys,v⟩
  cases ys <;> rfl

#print axioms queries

theorem semantic (xs : Array (WAdm_EmittedScalars.K) 10#usize) (out : alloc.vec.Vec U8) :
    WAdm_semantic out xs = WAdm_Fold.run WAdm_model.WAdm_putK xs.val out := by
  simp only [WAdm_semantic,WAdm_Fissioned.Array.Insts.CoreIterTraitsCollectIntoIteratorTIntoIter.into_iter,bind_tc_ok]
  unfold WAdm_semantic_loop WAdm_Fold.run
  apply congrArg (fun body => loop body (xs.val,out))
  funext state
  rcases state with ⟨ys,v⟩
  cases ys <;> rfl

#print axioms semantic

theorem coordinates (xs : Array (WAdm_EmittedScalars.K) 4#usize) (out : alloc.vec.Vec U8) :
    WAdm_coordinates out xs = WAdm_Fold.run WAdm_model.WAdm_putK xs.val out := by
  simp only [WAdm_coordinates,WAdm_Fissioned.Array.Insts.CoreIterTraitsCollectIntoIteratorTIntoIter.into_iter,bind_tc_ok]
  unfold WAdm_coordinates_loop WAdm_Fold.run
  apply congrArg (fun body => loop body (xs.val,out))
  funext state
  rcases state with ⟨ys,v⟩
  cases ys <;> rfl

#print axioms coordinates
end AspisR1.WAdm_LoopShapes
end
