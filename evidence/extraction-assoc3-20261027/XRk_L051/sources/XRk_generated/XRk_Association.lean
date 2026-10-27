import XRk_RejectedScratch
open Aeneas Aeneas.Std Result
open XRk_Release
namespace XRk_Association
abbrev E := aspis_core.field.wide_exact.WideExact
abbrev Q := aspis_core.field.QM31
/- These are concrete properties of the isolated emitted computation, in the
   requested order. Native source/reference P6, query effects, artifact binding
   and the security-top implementation instance are separate OPEN rows. -/
def PreparedScratchProjection : Prop :=
  ∀ (H : Type) (D : aspis_core.digest.Digest32 H) (sem : r1_semantic.Verified H)
    (v : verifier.View) (hash : H) (old : Array E 29#usize),
    match verifier.Prepared.new D sem v hash old with
    | .ok (.Ok p,scratch) => weights.powers 29#usize p.gamma = ok scratch
    | .ok (.Err _,scratch) => scratch = old ∨ ∃ gamma, weights.powers 29#usize gamma = ok scratch
    | .fail _ => True
    | .div => True

def PreparedClaimPowersAssociation : Prop :=
  ∀ (gamma : E) (scratch : Array E 29#usize),
    weights.powers 29#usize gamma = ok scratch →
    ∃ one, aspis_core.field.wide_exact.WideExact.ONE = ok one ∧
      XRk_powers gamma 29 one = ok scratch.val

def QueryGeometryLineInvariant : Prop :=
  ∀ (queries : Array U32 22#usize) (start finish : Usize) (g : verifier.QueryGeometry),
    verifier.QueryGeometry.for_range queries start finish = ok (.Ok g) →
    g.start = start ∧ g.inverses.val.length = finish.val-start.val ∧
    g.line_z.val.length = finish.val-start.val

def DotCountProjection : Prop :=
  ∀ (old next : fast_pairing.EbyKDot) (e : E) (q : Q),
    fast_pairing.EbyKDot.push old e q = ok (.Ok (),next) →
    old.count < 4096#usize ∧ old.count + 1#usize = ok next.count

def CandidateTx1AcceptedPath : Prop :=
  ∀ (H : Type) (D : aspis_core.digest.Digest32 H)
    (pub : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (physical proof : Slice U8) (split : Usize) (hash : H)
    (obs : Option (verifier.Phase → Result Unit)) (bytes : alloc.vec.Vec U8),
    verifier.candidate.tx1 D pub physical proof split hash obs = ok (.Ok bytes) →
    ∃ (p : verifier.Prepared) (scratch : Array E 29#usize) (zero : E),
      aspis_core.field.wide_exact.WideExact.ZERO = ok zero ∧
      verifier.candidate.prepare D pub proof hash obs (Array.repeat 29#usize zero) = ok (.Ok p,scratch) ∧
      split = compact.SPLIT ∧ weights.powers 29#usize p.gamma = ok scratch

def AcceptedCandidateCheckpoint : Prop :=
  ∀ (H : Type) (D : aspis_core.digest.Digest32 H)
    (pub : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (physical proof : Slice U8) (split : Usize) (hash : H)
    (obs : Option (verifier.Phase → Result Unit)) (bytes : alloc.vec.Vec U8),
    verifier.candidate.tx1 D pub physical proof split hash obs = ok (.Ok bytes) →
    ∃ (p : verifier.Prepared) (scratch : Array E 29#usize) (zero : E) (a : verifier.Accumulator),
      aspis_core.field.wide_exact.WideExact.ZERO = ok zero ∧
      verifier.candidate.prepare D pub proof hash obs (Array.repeat 29#usize zero) = ok (.Ok p,scratch) ∧
      verifier.checkpoint D p a proof physical hash = ok bytes

/- Only this result is supplied here. The following five named Props carry no
   theorem/instance/axiom and no top imports this file. -/
theorem preparedScratchProjection : PreparedScratchProjection := by
  intro H D sem v hash old
  cases h : verifier.Prepared.new D sem v hash old with
  | fail _ => trivial
  | div => trivial
  | ok r =>
    rcases r with ⟨r,scratch⟩
    cases r with
    | Ok p => exact XRk_ScratchProjection.accepted_powers D sem v hash old scratch p h
    | Err e => exact XRk_RejectedScratch.rejected_scratch D sem v hash old scratch e h
#print axioms preparedScratchProjection
end XRk_Association
