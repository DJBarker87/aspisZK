import F3S_FinishReached
import F3S_RoundUnique
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3S_FinishWitness
open Aeneas Aeneas.Std Result AspisR1Stage2 AspisR1Stage2.Stage2Finish
structure Primitives {W : Type} (ops : FinishOps W) (v : verifier.View) (p : verifier.Prepared)
    (a : verifier.Accumulator) where
  alpha0 : E
  alpha1 : E
  r0 : RowFinish_Control.RoundValues ops v.round0 alpha0 p.claim
  r1 : RowFinish_Control.RoundValues ops v.round1 alpha1 r0.value
  weights : W
  alphas : Slice E
  pair : E
  dot : E
  ha0 : Array.index_usize p.alpha 0#usize=ok alpha0
  ha1 : Array.index_usize p.alpha 1#usize=ok alpha1
  hw : ops.newWeights p.variant p.semantic_alpha p.z=ok (.Ok weights)
  has : core.array.Array.index (core.ops.index.IndexSlice
    (core.slice.index.SliceIndexRangeToUsizeSlice E)) p.alpha {«end»:=2#usize}=ok alphas
  hp : ops.pair weights alphas v.final_message p.kappa=ok (.Ok pair)
  hd : ops.dot v.final_message a.weights.deref=ok (.Ok dot)
 theorem source {W : Type} (ops : FinishOps W) (v : verifier.View) (p : verifier.Prepared)
    (a : verifier.Accumulator) (s2 : p.variant=.S2)
    (success : Port4D_FinishInstall.finish ops v p a none=ok (.Ok ())) :
    Nonempty (Primitives ops v p a) := by
  obtain ⟨alpha0,alpha1,value0,value1,weights,alphas,pair,dot,ha0,ha1,h0,h1,hw,has,hp,hd⟩ :=
    F3S_FinishReached.reached ops v p a s2 success
  obtain ⟨r0,er0⟩ := F3S_RoundValues.reached ops v.round0 alpha0 p.claim 0#usize value0 h0
  subst value0
  obtain ⟨r1,er1⟩ := F3S_RoundValues.reached ops v.round1 alpha1 r0.value 1#usize value1 h1
  exact ⟨⟨alpha0,alpha1,r0,r1,weights,alphas,pair,dot,ha0,ha1,hw,has,hp,hd⟩⟩
#print axioms source
end AspisR1.F3S_FinishWitness
end
