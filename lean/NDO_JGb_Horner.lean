import NDO_FIv_FoldsTotal
import NDO_JGa_ChallengeCanonical
import RPv_JFy_PreparedSteps
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGb_Horner
open Aeneas Aeneas.Std Result WP FIq_Native
open FIv_NativeValue (Canon decode)
open FIw_ArrayValue (canonical)
open pool_v1.pair_forest_semantic_terminal

/-- The actual reverse-iterator setup used by composition, with its two folds. -/
def run (sem : Array field.QM31 24#usize) (pos : Array field.QM31 4#usize)
    (theta seed : field.QM31) : Result field.QM31 := do
  let p ← field.PreparedQm31Multiplier.new theta
  let ii ← FIq_Native.Array.Insts.CoreIterTraitsCollectIntoIteratorTIntoIter.into_iter sem
  let it ← core.iter.traits.iterator.Iterator.rev.trait_default
    (core.array.iter.IntoIter.Insts.CoreIterTraitsIteratorIterator field.QM31 24#usize)
    (core.array.iter.IntoIter.Insts.CoreIterTraitsDouble_endedDoubleEndedIterator field.QM31 24#usize) ii
  let mid ← composition_parts_loop0 it p seed
  let ii1 ← FIq_Native.Array.Insts.CoreIterTraitsCollectIntoIteratorTIntoIter.into_iter pos
  let it1 ← core.iter.traits.iterator.Iterator.rev.trait_default
    (core.array.iter.IntoIter.Insts.CoreIterTraitsIteratorIterator field.QM31 4#usize)
    (core.array.iter.IntoIter.Insts.CoreIterTraitsDouble_endedDoubleEndedIterator field.QM31 4#usize) ii1
  composition_parts_loop1 it1 p mid

theorem source (sem : Array field.QM31 24#usize) (pos : Array field.QM31 4#usize)
    (theta seed : field.QM31) (ht : Canon theta) (hs : Canon seed)
    (hsem : canonical sem) (hpos : canonical pos) :
    ∃ out,run sem pos theta seed=ok out ∧ Canon out ∧
      decode out=FIv_CompositionValue.polynomial (decode theta) sem pos seed := by
  exact FIv_FoldsTotal.value sem pos theta seed ht hs hsem hpos
#print axioms source
end AspisR1.JGb_Horner
end
