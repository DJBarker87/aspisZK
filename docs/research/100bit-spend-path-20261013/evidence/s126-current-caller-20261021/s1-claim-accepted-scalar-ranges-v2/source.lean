import CurrentClaimScalarReads
import ClaimDotConcreteAdapterV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisS1ClaimAcceptedScalarRanges
open AspisR1CurrentPreparedClaim
open AspisR1S5ClaimDotConcreteAdapter
abbrev Q := aspis_core.field.QM31
abbrev E := aspis_core.field.WideExact
abbrev RawFn := AspisR1EbyKPushDotBackend.RawFn

def ScalarCanonical (q : Q) : Prop :=
  ∀ w ∈ [q.c0.a,q.c0.b,q.c1.a,q.c1.b], w.val < 2147483647

/-- The concrete checked-Q guard supplies the input range. No scalar range,
raw arithmetic interpretation, or independently successful child is assumed. -/
theorem accepted_push_scalar_ranges (rawFn : RawFn) (before after : PushState)
    (value : E) (scalar : Q)
    (h : (concreteOps rawFn).pushDot before value scalar = ok (.Ok (),after)) :
    ScalarCanonical scalar := by
  exact AspisR1EbyKPushCheckedScalarCanonical.successful_push_scalar_canonical
    (AspisR1EbyKPushDotBackend.dotViaRaw rawFn) before (toPushWide value)
    (toPushQm scalar) after h

/-- Every reached index in the SAME successful extracted source chain has a
checked canonical scalar; no fresh or separately successful read is supplied. -/
theorem chain_read_ranges {H : Type} (rawFn : RawFn)
    (sem : r1_semantic.Verified H) (y1 : Slice U8) (g : Array E 29#usize)
    (point : Usize) {iter : ClaimScalar.Range} {dot : PushState} {out : E}
    (trace : ClaimScalar.Chain (concreteOps rawFn) sem y1 g point iter dot out) :
    ∀ l : Usize, iter.start.val ≤ l.val → l.val < 29 →
      ∃ scalar, ClaimScalar.read (concreteOps rawFn) sem y1 point l = ok scalar ∧
        ScalarCanonical scalar := by
  induction trace with
  | done r d x he hf =>
    intro l lower upper
    omega
  | @step r r' d d' x l coeff scalar hn hr hw hp tail ih =>
    intro target lower upper
    obtain ⟨headEq,active,nextStart,nextEnd⟩ := ClaimTrace.next_some_step r r' l hn
    by_cases same : target = l
    · subst target
      exact ⟨scalar,hr,accepted_push_scalar_ranges rawFn d d' coeff scalar hp⟩
    · apply ih target ?_ upper
      have different : target.val ≠ l.val := fun h => same (UScalar.eq_of_val_eq h)
      have head : l.val = r.start.val := congrArg UScalar.val headEq
      omega

theorem accepted_helper_read_ranges {H : Type} (rawFn : RawFn)
    (D : aspis_core.Digest32 H) (sem : r1_semantic.Verified H)
    (y1 : Slice U8) (g : Array E 29#usize) (point : Usize) (out : E)
    (accepted : verifier.prepared_claim_dot (concreteOps rawFn) D sem y1 g point = ok (.Ok out)) :
    ∀ l : Usize, l.val < 29 →
      ∃ scalar, ClaimScalar.read (concreteOps rawFn) sem y1 point l = ok scalar ∧
        ScalarCanonical scalar := by
  obtain ⟨dot,xs,newDot,trace,rest⟩ :=
    ClaimScalar.successful_helper_has_exact_reads (concreteOps rawFn) D sem y1 g point out accepted
  intro l bound
  exact chain_read_ranges rawFn sem y1 g point trace l (by simp) bound

/-- All six successful helpers are derived from this same enclosing claim.
Kappa canonicality is retained only for the existing source outer-chain join. -/
theorem accepted_claim_read_ranges {H : Type} (rawFn : RawFn)
    (D : aspis_core.Digest32 H) (sem : r1_semantic.Verified H)
    (y1 : Slice U8) (inactive kappa out : E) (g : Array E 29#usize)
    (hk : Concrete.Canonical kappa)
    (accepted : verifier.prepared_claim (concreteOps rawFn) D sem y1 inactive g kappa = ok (.Ok out)) :
    ∀ point : Usize, point.val < 6 → ∀ l : Usize, l.val < 29 →
      ∃ scalar, ClaimScalar.read (concreteOps rawFn) sem y1 point l = ok scalar ∧
        ScalarCanonical scalar := by
  have installed : ClaimPowers.withConcretePowers (concreteOps rawFn) = concreteOps rawFn := rfl
  obtain ⟨k,parts,powers,initial,trace⟩ := successful_concrete_claim_has_powered_chain
    rawFn D sem y1 inactive kappa out g hk (by simpa only [installed] using accepted)
  rw [installed] at trace
  obtain ⟨xs,length,order,calls⟩ := ClaimTrace.chain_has_ordered_calls trace (by rfl) (by simp)
  intro point pointBound l bound
  have size : xs.length = 6 := by simpa using length
  have idx : point.val < xs.length := by omega
  have same : (xs[point.val]'idx).1 = point := by
    apply UScalar.eq_of_val_eq
    simpa using order point.val idx
  have called := calls (xs[point.val]'idx) (List.getElem_mem idx)
  rw [same] at called
  exact accepted_helper_read_ranges rawFn D sem y1 g point _ called l bound

#print axioms accepted_push_scalar_ranges
#print axioms chain_read_ranges
#print axioms accepted_helper_read_ranges
#print axioms accepted_claim_read_ranges
end AspisS1ClaimAcceptedScalarRanges
