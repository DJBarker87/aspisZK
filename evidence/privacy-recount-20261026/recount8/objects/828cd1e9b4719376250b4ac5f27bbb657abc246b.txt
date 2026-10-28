import R1Z.ProverRwP6ArrayMap
import AspisR1ProducerRelease47.Powers48
import R1Z.ProverCommitGamma48
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverRwP6PowersNativeStep
open Aeneas Aeneas.Std Result ProverRwFull
abbrev W := aspis_core.field.wide_exact.WideExact
abbrev NW := AspisR1ProducerRelease47.field.wide_exact.WideExact
abbrev toW := ProverRwDictionaryTower.toW
abbrev fromW := ProverRwDictionaryTower.fromW
abbrev dict [ExternalTypes] := ProverRwP6BoundaryInstall.selected
def finish {N : Usize} (r : ProverRwP6PowersControl.Ret N) : Array W N :=
  match r.2 with
  | none => r.1
  | some out => out
def nativeArray {N : Usize} (out : Array W N) : Array NW N := ProverRwP6ArrayMap.map toW out

theorem read {N : Usize} (out : Array W N) (i : Usize) (hi : i.val<N.val) :
    ∃ v, Array.index_mut_usize out i = ok (v,Aeneas.Std.Array.set out i) ∧
      Array.index_mut_usize (nativeArray out) i = ok (toW v,Aeneas.Std.Array.set (nativeArray out) i) := by
  obtain ⟨v,hv⟩ := ProverRwP6ArrayRead.read out i hi
  have hn : Array.index_usize (nativeArray out) i = ok (toW v) := by
    rw [nativeArray,ProverRwP6ArrayMap.index,hv]
    rfl
  refine ⟨v,?_,?_⟩ <;> unfold Array.index_mut_usize
  · rw [hv]; rfl
  · rw [hn]; rfl

theorem mul [ExternalTypes] (ops : ExternalFuns) (p x : W) :
    ∃ q, AspisR1ProducerRelease47.field.wide_exact.WideExact.mul (toW p) (toW x) = ok q ∧
      (dict ops).op47 p x = ok (fromW q) := by
  obtain ⟨q,hq⟩ := ProverRwP6WideTotal.mul (toW p) (toW x)
  refine ⟨q,hq,?_⟩
  change ProverRwDictionaryTower.mapResult fromW
    (AspisR1ProducerRelease47.field.wide_exact.WideExact.mul (toW p) (toW x)) = _
  rw [hq]
  rfl

theorem set {N : Usize} (out : Array W N) (i : Usize) (p : W) :
    nativeArray (Aeneas.Std.Array.set out i p) = Aeneas.Std.Array.set (nativeArray out) i (toW p) :=
  ProverRwP6ArrayMap.set_map toW out i p
#print axioms read
#print axioms mul
#print axioms set
end R1Z.ProverRwP6PowersNativeStep
