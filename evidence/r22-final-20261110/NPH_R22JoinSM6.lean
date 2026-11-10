import NPH_R22JoinSM5
import NOM_TerminalDomain
import CurrentCompactCallerModelV1

/-! NPH_ (R22, SM step 5): the digest-domain premise of NPH_R22JoinSM5.slot_guarded from the 345
statement validation, carried through the tx1 candidate.
- `prepare_op9_congr`: verifier.candidate.prepare with op9 replaced by f equals the original
  whenever f agrees with op9 at the prepare's OWN public (every other argument free). The
  prepare calls op9 only at its own public1 (with its hash and obs).
- `tx1_op9_congr`: the same for verifier.candidate.tx1, which calls op9 only through
  candidate.prepare at its own public1 (the other ops slots and the irreducible constants
  ZERO/OFF_FOLDED_ROOT/OFF_ROUND1 do not read op9: zero9/ofr9/or19).
- `digest_of_binding`: if the current public cp is FirstComposition.toCurrentPublic of the
  library semantic public of a statement st whose installed op21 validate returned Ok, then
  publicDigestDom (toRetainedPublic cp) (NOC_Op9Slot.pub_round, NOM_TerminalDomain.validated_digest).
  This is the 345 binding: NOC_Stage1Forward.publicBinding gives exactly
  AspisS6CurrentVerifierCarrier.toPublic sp = toCurrentPublic (C.semanticPublic (carrier st))
  for the semantic public sp that stage1_owned passes to first_decoded after the op21 success
  (NOC_Stage1Forward.body hypotheses val21/spRun/fd; NOC_Stage1Forward.fdLemma unfolds
  first_decoded (S c) sp to this tx1 at that public, hash () and obs none).
- `tx1_guarded`: at every host context, for such a public, the deployed tx1 candidate equals the
  same tx1 whose op9 slot on release `none` is the guarded semantic installation over
  NPH_R22JoinSM5.Bslot (mask/add/mul run only on canonical arguments). Standard axioms. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.NPH_R22JoinSM6
open Aeneas Aeneas.Std Result
open AspisR1CurrentCaller

abbrev Op9 := ∀ {H : Type}, aspis_core.digest.Digest32 H →
  aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public → Slice U8 → H →
  Option (verifier.Phase → Result Unit) → Result (core.result.Result (r1_semantic.Verified H) r1_wire.Error)

theorem ls9 (O : Ops) (f : Op9) :
    compact.LOGICAL_SEMANTIC { O with op9 := f } = compact.LOGICAL_SEMANTIC O := by
  unfold compact.LOGICAL_SEMANTIC; rfl
#print axioms ls9
theorem os9 (O : Ops) (f : Op9) :
    compact.OFF_SEMANTIC { O with op9 := f } = compact.OFF_SEMANTIC O := by
  unfold compact.OFF_SEMANTIC; rfl
#print axioms os9
theorem oy9 (O : Ops) (f : Op9) :
    compact.OFF_Y1 { O with op9 := f } = compact.OFF_Y1 O := by
  unfold compact.OFF_Y1 compact.OFF_SEMANTIC; rfl
#print axioms oy9
theorem oi9 (O : Ops) (f : Op9) :
    compact.OFF_INACTIVE { O with op9 := f } = compact.OFF_INACTIVE O := by
  unfold compact.OFF_INACTIVE compact.OFF_Y1 compact.OFF_SEMANTIC; rfl
#print axioms oi9
theorem zero9 (O : Ops) (f : Op9) :
    aspis_core.field.wide_exact.WideExact.ZERO { O with op9 := f } =
      aspis_core.field.wide_exact.WideExact.ZERO O := by
  unfold aspis_core.field.wide_exact.WideExact.ZERO; rfl
#print axioms zero9
theorem ofr9 (O : Ops) (f : Op9) :
    compact.OFF_FOLDED_ROOT { O with op9 := f } = compact.OFF_FOLDED_ROOT O := by
  unfold compact.OFF_FOLDED_ROOT; rfl
#print axioms ofr9
theorem or19 (O : Ops) (f : Op9) :
    compact.OFF_ROUND1 { O with op9 := f } = compact.OFF_ROUND1 O := by
  unfold compact.OFF_ROUND1 compact.OFF_FOLDED_ROOT; rfl
#print axioms or19

theorem prepare_op9_congr (O : Ops) (f : Op9) {H : Type} (D : aspis_core.digest.Digest32 H)
    (pub : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (proof : Slice U8) (hash : H) (obs : Option (verifier.Phase → Result Unit))
    (g : Array aspis_core.field.wide_exact.WideExact 29#usize)
    (hagree : ∀ b : Slice U8, f D pub b hash obs = O.op9 D pub b hash obs) :
    verifier.candidate.prepare { O with op9 := f } D pub proof hash obs g =
      verifier.candidate.prepare O D pub proof hash obs g := by
  unfold verifier.candidate.prepare
  simp only [ls9, os9, oy9, oi9, hagree]
#print axioms prepare_op9_congr

theorem tx1_op9_congr (O : Ops) (f : Op9) {H : Type} (D : aspis_core.digest.Digest32 H)
    (pub : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (pubBytes proof : Slice U8) (k : Usize) (hash : H) (obs : Option (verifier.Phase → Result Unit))
    (hagree : ∀ b : Slice U8, f D pub b hash obs = O.op9 D pub b hash obs) :
    verifier.candidate.tx1 { O with op9 := f } D pub pubBytes proof k hash obs =
      verifier.candidate.tx1 O D pub pubBytes proof k hash obs := by
  have hp : ∀ g, verifier.candidate.prepare { O with op9 := f } D pub proof hash obs g =
      verifier.candidate.prepare O D pub proof hash obs g :=
    fun g => prepare_op9_congr O f D pub proof hash obs g hagree
  unfold verifier.candidate.tx1
  simp only [zero9, ofr9, or19, hp]
#print axioms tx1_op9_congr

theorem digest_of_binding (st : NNH_S1HostCodec.Statement)
    (good : NNH_S1HostCodec.validate st = .ok (.Ok ()))
    (cp : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (spEq : cp = FirstComposition.toCurrentPublic
      (NNH_Libraries.C.semanticPublic (NNH_S1DecodeOk.carrier st))) :
    LIB_VPublicDomain.publicDigestDom (FirstComposition.toRetainedPublic cp) := by
  rw [spEq, NOC_Op9Slot.pub_round]
  exact NOM_TerminalDomain.validated_digest st good
#print axioms digest_of_binding

/-- The op9 slot with the guarded semantic installation on release `none`. -/
def op9g (r : NP6_StdModel.Reservation) (O : Ops) : Op9 := fun {H} D pub b h o =>
  match o with
  | none => S1SemanticInstallation.verify AspisS1ExtractedRoundChildren.children
      (NPH_R22JoinSM5.Bslot r) D pub b h
  | some ob => O.op9 D pub b h (some ob)

theorem tx1_guarded {W Tx : Type} (c : NNH_Run5bCtx.Ctx W Tx) (st : NNH_S1HostCodec.Statement)
    (good : NNH_S1HostCodec.validate st = .ok (.Ok ()))
    (cp : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (spEq : cp = FirstComposition.toCurrentPublic
      (NNH_Libraries.C.semanticPublic (NNH_S1DecodeOk.carrier st)))
    (D : aspis_core.digest.Digest32 Unit) (pubBytes proof : Slice U8) (k : Usize) :
    verifier.candidate.tx1
        { DrvC_Installation.currentInstalled (NNH_Run5bCtx.configuration c) with
          op9 := op9g c.fixed.reservation (DrvC_Installation.currentInstalled (NNH_Run5bCtx.configuration c)) }
        D cp pubBytes proof k () none =
      verifier.candidate.tx1 (DrvC_Installation.currentInstalled (NNH_Run5bCtx.configuration c))
        D cp pubBytes proof k () none := by
  apply tx1_op9_congr
  intro b
  show S1SemanticInstallation.verify AspisS1ExtractedRoundChildren.children
      (NPH_R22JoinSM5.Bslot c.fixed.reservation) D cp b () = _
  exact (NPH_R22JoinSM5.slot_guarded c D cp b (digest_of_binding st good cp spEq)).symm
#print axioms tx1_guarded

end AspisR1.NPH_R22JoinSM6
