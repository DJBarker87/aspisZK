import V7CallerCurrentReleaseR26FieldBridge
import V7CallerCurrentReleaseR26QueryScaleLoop

open Aeneas Aeneas.Std Result ControlFlow Error
open V7CallerCurrentReleaseR26

namespace V7CallerCurrentReleaseR26QueryScaleExactStep

open V7CallerCurrentReleaseR26FieldBridge

local instance : Inhabited field.QM31 := ⟨field.QM31.ZERO⟩

def CanonicalScaleArray (values : Array field.QM31 16#usize) : Prop :=
  ∀ index : Nat, index < 16 →
    GeneratedCanonicalQM31 values.val[index]!

theorem scale_array_set_same
    (values : Array field.QM31 16#usize) (index : Std.Usize)
    (value : field.QM31) (hindex : index.val < 16) :
    (values.set index value).val[index.val]! = value := by
  simp only [Array.set_val_eq]
  apply List.set_getElem!_eq
  exact ⟨by simpa [Array.length_eq] using hindex, rfl⟩

theorem scale_array_set_ne
    (values : Array field.QM31 16#usize) (index : Std.Usize)
    (value : field.QM31) (other : Nat) (hne : other ≠ index.val) :
    (values.set index value).val[other]! = values.val[other]! := by
  apply List.set_getElem!_ne
  omega

theorem canonical_scale_array_set
    (values : Array field.QM31 16#usize) (index : Std.Usize)
    (value : field.QM31) (hindex : index.val < 16)
    (hvalues : CanonicalScaleArray values)
    (hvalue : GeneratedCanonicalQM31 value) :
    CanonicalScaleArray (values.set index value) := by
  intro other hother
  by_cases hsame : other = index.val
  · subst other
    rw [scale_array_set_same values index value hindex]
    exact hvalue
  · rw [scale_array_set_ne values index value other hsame]
    exact hvalues other hother

theorem shifted_scale_seed_canonical
    (rho : field.QM31) (seed : Array field.QM31 16#usize)
    (hrho : GeneratedCanonicalQM31 rho)
    (hseed : Array.update (Array.repeat 16#usize field.QM31.ZERO)
      0#usize rho = ok seed) :
    CanonicalScaleArray seed ∧ seed.val[0]! = rho := by
  have hupdate := Array.update_spec
    (Array.repeat 16#usize field.QM31.ZERO) 0#usize rho (by norm_num)
  obtain ⟨updated, hupdateRun, hupdateEq⟩ := WP.spec_imp_exists hupdate
  have hseedEq : seed = updated := Result.ok.inj (hseed.symm.trans hupdateRun)
  have hseedSet : seed = (Array.repeat 16#usize field.QM31.ZERO).set 0#usize rho :=
    hseedEq.trans hupdateEq
  clear hupdate hupdateRun hupdateEq hseed hseedEq
  rw [hseedSet]
  constructor
  · apply canonical_scale_array_set
    · norm_num
    · intro index hindex
      rw [Array.repeat_val]
      change GeneratedCanonicalQM31
        (List.replicate 16 field.QM31.ZERO)[index]!
      rw [List.getElem!_replicate field.QM31.ZERO hindex]
      exact V7CallerCurrentReleaseR26FieldBridge.generated_qm31_zero_canonical
    · exact hrho
  · apply scale_array_set_same
    norm_num

def exactScaleAt (values : Array field.QM31 16#usize) (index : Nat) :
    ExactQM31 :=
  generatedQm31ToExact values.val[index]!

def ShiftedScalePrefix (rhoExact : ExactQM31)
    (values : Array field.QM31 16#usize) (extent : Std.Usize) : Prop :=
  CanonicalScaleArray values ∧ 1 ≤ extent.val ∧ extent.val ≤ 16 ∧
    ∀ index : Nat, index < extent.val →
      exactScaleAt values index = rhoExact ^ (index + 1)

theorem shifted_scale_seed_prefix
    (rho : field.QM31) (seed : Array field.QM31 16#usize)
    (rhoExact : ExactQM31)
    (hrho : GeneratedCanonicalQM31 rho)
    (hrhoExact : generatedQm31ToExact rho = rhoExact)
    (hseed : Array.update (Array.repeat 16#usize field.QM31.ZERO)
      0#usize rho = ok seed) :
    ShiftedScalePrefix rhoExact seed 1#usize := by
  obtain ⟨hcanonical, hzero⟩ := shifted_scale_seed_canonical rho seed hrho hseed
  refine ⟨hcanonical, by norm_num, by norm_num, ?_⟩
  intro index hindex
  have hOne : (1#usize).val = 1 := rfl
  have hindexZero : index = 0 := by
    rw [hOne] at hindex
    omega
  subst index
  unfold exactScaleAt
  rw [hzero, hrhoExact]
  norm_num

/-- A successful source iteration of the shifted-query scale loop has the
exact multiplicative meaning required for the rho-power covector.  This keeps
the generated iterator transition symbolic while using the source-authentic
prepared multiplier semantics. -/
theorem scale_loop_body_step_exact
    (rho prior next : field.QM31)
    (prepared : field.PreparedQm31Multiplier)
    (iter iterNext : core.ops.range.Range Std.Usize)
    (scales scalesNext : Array field.QM31 16#usize)
    (ordinal predecessor : Std.Usize)
    (hrho : GeneratedCanonicalQM31 rho)
    (hprior : GeneratedCanonicalQM31 prior)
    (hnew : field.PreparedQm31Multiplier.impl.new rho = ok prepared)
    (hNext : core.iter.range.IteratorRange.next core.iter.range.StepUsize iter =
      ok (some ordinal, iterNext))
    (hPredecessor : Std.Usize.wrapping_sub ordinal 1#usize = predecessor)
    (hIndex : Array.index_usize scales predecessor = ok prior)
    (hMultiply : field.PreparedQm31Multiplier.impl.mul prepared prior = ok next)
    (hUpdate : Array.update scales ordinal next = ok scalesNext) :
    GeneratedCanonicalQM31 next ∧
      generatedQm31ToExact next =
        generatedQm31ToExact rho * generatedQm31ToExact prior ∧
      v6_query_batch.add_final256_query_batch_with_initial_scale_loop.body
          prepared iter scales = ok (cont (iterNext, scalesNext)) := by
  obtain ⟨hcanonical, hexact⟩ := generated_prepared_qm31_mul_exact rho prior next
    prepared hrho hprior hnew hMultiply
  exact ⟨hcanonical, hexact,
    V7CallerCurrentReleaseR26QueryScaleLoop.scale_loop_body_step prepared iter
      iterNext scales scalesNext ordinal predecessor prior next hNext hPredecessor
      hIndex hMultiply hUpdate⟩

#print axioms shifted_scale_seed_prefix
#print axioms shifted_scale_seed_canonical
#print axioms scale_loop_body_step_exact

end V7CallerCurrentReleaseR26QueryScaleExactStep
