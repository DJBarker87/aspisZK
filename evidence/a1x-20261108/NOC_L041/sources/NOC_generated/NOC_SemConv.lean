import NOC_ConvSemantic
import NOC_Op9Slot
import NOM_TerminalDomain
set_option autoImplicit false
noncomputable section
namespace AspisR1.NOC_SemConv
open Aeneas Aeneas.Std Result AspisR1PublicPreparation LIB_VCarriers RSL

/-! Converse kit: inversion of one native bind, stepping a hypothesis by a
full Result equality, and stepping a library `bindValue` chain. -/

theorem bindInv {α β : Type} {m : Aeneas.Std.Result α} {k : α → Aeneas.Std.Result β} {r : β}
 (h : (m >>= k) = .ok r) : ∃ x, m = .ok x ∧ k x = .ok r := by
 cases m with
 | ok x => exact ⟨x, rfl, h⟩
 | fail e => first | cases h | simp [Bind.bind] at h
 | div => first | cases h | simp [Bind.bind] at h

theorem stepInv {α β : Type} {m : Aeneas.Std.Result α} {v : α} {k : α → Aeneas.Std.Result β}
 {r : Aeneas.Std.Result β} (hm : m = .ok v) (h : (m >>= k) = r) : k v = r := by
 subst hm; exact h

theorem bvStep {E A B : Type} {x : Except E A} {a : A} {k : A → Except E B} (hx : x = .ok a) :
 NNH_ReturnedRE.bindValue x k = k a := by subst hx; rfl

theorem mapEOk {E F A : Type} (f : E → F) {r : Except E A} {a : A} (h : r = .ok a) :
 RSL.RE.mapE f r = .ok a := by subst h; rfl

theorem ifOk {p : Prop} (inst : Decidable p) {E : Type} {e : E} (hp : ¬ p) :
 (if @decide p inst then Except.error e else Except.ok ()) = Except.ok () := by
 have d : @decide p inst = false := @decide_eq_false p inst hp
 rw [d]; rfl

theorem gateOk {Q : Type} {x y : Q} (inst : Decidable (x ≠ y)) {E : Type} {e : E} (hxy : x = y) :
 (if @decide (x ≠ y) inst then Except.error e else Except.ok ()) = Except.ok () :=
 ifOk inst (fun hne => hne hxy)

theorem distinctOk {P : Type} {x y : P} (inst : Decidable (x = y)) {E : Type} {e : E} (hxy : x ≠ y) :
 (if @decide (x = y) inst then Except.error e else Except.ok ()) = Except.ok () :=
 ifOk inst hxy

end AspisR1.NOC_SemConv

/-- Hypothesis normalization only (tuple destructuring, `?` on a known
constructor, phase marks, decided Boolean guards). -/
syntax "nci_nrh " ident : tactic
macro_rules
 | `(tactic| nci_nrh $h) => `(tactic| ((try simp only [Aeneas.Std.uncurry_apply_pair] at $h:ident); (try simp only [Aeneas.Std.uncurry] at $h:ident); (try simp only [bind_tc_ok, core.result.Result.Insts.CoreOpsTry.branch, AspisR1PublicPreparation.VerifyPrefix.mark, Bool.false_eq_true, ↓reduceIte] at $h:ident); (try simp only [bind_tc_ok, core.result.Result.Insts.CoreOpsTry.branch, Bool.false_eq_true, ↓reduceIte] at $h:ident)))

/-- Closes a branch whose continuation returns a non-Ok reply (Err residual,
error arm, unwrap of Err) against an `= ok (.Ok _)` hypothesis. -/
syntax "nci_kill " ident : tactic
macro_rules
 | `(tactic| nci_kill $h) => `(tactic| focus first
   | (cases $h:ident; done)
   | (simp only [bind_tc_ok, core.result.Result.Insts.CoreOpsTry.branch, core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual, ↓reduceIte] at $h:ident; done)
   | (simp only [bind_tc_ok, core.result.Result.Insts.CoreOpsTry.branch, core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual] at $h:ident
      obtain ⟨_, _, hk__⟩ := AspisR1.NOC_SemConv.bindInv $h
      first | (cases hk__; done) | (simp at hk__; done)
            | (obtain ⟨_, _, hk2__⟩ := AspisR1.NOC_SemConv.bindInv hk__; first | (cases hk2__; done) | (simp at hk2__; done)))
   | (obtain ⟨_, hk3__, hr3__⟩ := AspisR1.NOC_SemConv.bindInv $h; cases hk3__; nci_kill hr3__)
   | (simp at $h:ident; done))

/-- Steps a hypothesis `(m >>= k) = r` by a full Result equality `m = ok v`. -/
syntax "nci_step " ident term : tactic
macro_rules
 | `(tactic| nci_step $h $e) => `(tactic| first
   | (replace $h:ident := AspisR1.NOC_SemConv.stepInv $e $h; nci_nrh $h)
   | (nci_nrh $h; replace $h:ident := AspisR1.NOC_SemConv.stepInv $e $h; nci_nrh $h)
   | (replace $h:ident := AspisR1.NOC_SemConv.stepInv rfl $h; nci_nrh $h; replace $h:ident := AspisR1.NOC_SemConv.stepInv $e $h; nci_nrh $h))

namespace AspisR1.NOC_SemConv
open Aeneas Aeneas.Std Result AspisR1PublicPreparation LIB_VCarriers RSL
abbrev V := NNH_FinishReturns.V

theorem toRawInj (x y : LIB_VScalarCarriers.QM31)
 (h : LIB_VScalarCarriers.toRaw x = LIB_VScalarCarriers.toRaw y) : x = y := by
 apply Subtype.ext
 have e := congrArg LIB_VScalarCarriers.toNative h
 simp only [LIB_VScalarCarriers.toRaw, LIB_VScalarCarriers.native_roundtrip] at e
 exact e

/-- The native QM31 `ne` is the negated equality decision. -/
theorem qmNeFalse (x y : aspis_core.field.QM31)
 (h : core.cmp.PartialEq.ne.trait_default aspis_core.field.QM31.Insts.CoreCmpPartialEqQM31 x y = .ok false) :
 x = y := by
 refine Classical.byContradiction (fun hne => ?_)
 have t : core.cmp.PartialEq.ne.trait_default aspis_core.field.QM31.Insts.CoreCmpPartialEqQM31 x y = .ok true := by
  simp only [core.cmp.PartialEq.ne.trait_default,core.cmp.PartialEq.ne.default,
   aspis_core.field.QM31.Insts.CoreCmpPartialEqQM31,NNX_Comparisons.qm_eq,bind_tc_ok]
  first
   | (simp [hne]; done)
   | (simp only [hne, decide_false, Bool.not_false]; done)
   | (rw [decide_eq_false hne]; rfl)
 rw [t] at h
 cases h

theorem pointRefl (x : aspis_core.circle.SecureCirclePoint) : FinishModel.pointEq x x = .ok true := by
 rw [FinishModel.pointEq,NNX_Comparisons.qm_eq,bind_tc_ok]
 first
  | (rw [if_pos (by simp),NNX_Comparisons.qm_eq]; simp)
  | (simp [NNX_Comparisons.qm_eq]; done)
  | (simp only [decide_true, if_true, NNX_Comparisons.qm_eq]; done)

theorem pointNe (x y : aspis_core.circle.SecureCirclePoint) (h : FinishModel.pointEq x y = .ok false) : x ≠ y := by
 intro e
 subst e
 rw [pointRefl] at h
 cases h

/-- An Ok 32-byte copy reads a 32-byte slice. -/
theorem tryLen (s : Slice U8) (arr : Array U8 32#usize)
 (h : core.array.TryFromArrayCopySlice.try_from 32#usize core.marker.CopyU8 s = .ok (.Ok arr)) :
 s.val.length = 32 := by
 unfold core.array.TryFromArrayCopySlice.try_from at h
 split at h
 · rename_i hl
   first
    | (simpa [Slice.length] using hl)
    | (simp only [Slice.length] at hl; scalar_tac)
    | (have := congrArg UScalar.val hl; simpa [Slice.length] using this)
    | scalar_tac
 · first | cases h | simp at h

theorem rootConv (s : Slice U8) (arr : Array U8 32#usize)
 (h : core.array.TryFromArrayCopySlice.try_from 32#usize core.marker.CopyU8 s = .ok (.Ok arr)) :
 ∃ root, TX1_136.toB32 (LIB_Carriers.bytes s) = some root := by
 have l : (LIB_Carriers.bytes s).length = 32 := by
  simp only [LIB_Carriers.bytes,NMS_R2N_RSLScalars.bytes,List.length_map]
  exact tryLen s arr h
 refine ⟨⟨LIB_Carriers.bytes s, l⟩, ?_⟩
 first
  | exact dif_pos l
  | (unfold TX1_136.toB32; rw [dif_pos l])
  | (simp only [TX1_136.toB32, l, dif_pos])
  | (simp [TX1_136.toB32, l])

/-- Converse of NOC_FinishSource.source: an Ok native semantic finish at the
installed boundaries gives an ok returned library finish value. The terminal
child is the NOM terminal port on the Domain from the SAME returned public
transcript and the validated public digest. -/
theorem finish (a : TX1_136.Args V) (env : Env) (granted : env.reservation = true)
 (digest : LIB_VPublicDomain.publicDigestDom a.public_) (rr : B32) (t0 : Transcript)
 (tr : LIB_VLib.publicTranscriptValue (a.public_,rr) env = .ok t0)
 (called : ∃ out, FinishModel.finish AspisS1ExtractedRoundChildren.children NOC_FinishSource.Bi
   (LIB_VCode.digest env) a.public_ (prefixRaw a.prefix_) a.transcript (challengesRaw a.challenges) none =
   .ok (.Ok out)) :
 ∃ sem, NNH_FinishReturns.value a env = .ok sem := by
 obtain ⟨out, h⟩ := called
 unfold FinishModel.finish at h
 nci_nrh h
 -- rounds
 obtain ⟨raw | _, h1, h⟩ := bindInv h; rotate_left; nci_kill h
 obtain ⟨r, hr, hraw⟩ := NOC_ConvSemantic.rounds a.prefix_ a.transcript env raw h1
 subst hraw
 nci_nrh h
 -- claims (an equality at the granted reservation)
 have cl := NOC_ConvSemantic.claims a.prefix_ env granted
 nci_step h cl.2
 -- terminal
 obtain ⟨traw | _, h3, h⟩ := bindInv h; rotate_left; nci_kill h
 have dom := NOM_TerminalDomain.domain (a.public_,LIB_VClaims.value a.prefix_,r.2.1,V.origChallenges a.challenges)
  rr env t0 digest tr
 obtain ⟨q, hq, hqraw⟩ := NOM_TerminalDomain.terminal _ env dom traw h3
 subst hqraw
 nci_step h rfl
 -- c1 gather, mask rows, mask
 nci_step h (NNX_C1Gather.source (LIB_VCode.digest env) (LIB_VClaims.value a.prefix_))
 nci_step h (NNX_Mask10.source (LIB_VCode.digest env) (LIB_VClaims.value a.prefix_))
 nci_step h (NNX_ClaimPorts.row (LIB_VClaims.value a.prefix_))
 nci_step h (NNX_ClaimPorts.at27 (LIB_VClaims.value a.prefix_))
 nci_step h (LIB_VField.mask_exact (LIB_VClaims.value a.prefix_) r.2.1)
 -- record 25 and its K29 decode
 obtain ⟨rec25 | _, h5, h⟩ := bindInv h; rotate_left; nci_kill h
 have hrec25 := NOC_ConvSemantic.record a.prefix_ 25#u8 rec25 h5
 nci_nrh h
 obtain ⟨xraw | _, h6, h⟩ := bindInv h; rotate_left; nci_kill h
 obtain ⟨extra, hextra, hxraw⟩ := NOC_ConvSemantic.decode rec25 87#usize
  (NNV_FinishDecodeDomains.extra a.prefix_ rec25 hrec25) xraw h6
 subst hxraw
 nci_nrh h
 -- masked terminal
 nci_step h (LIB_VField.qmul_exact (LIB_VCarriers.eta a.challenges) q)
 nci_step h (LIB_VField.qadd_exact (LIB_VField.maskValue (LIB_VClaims.value a.prefix_) r.2.1)
  (LIB_VField.qmul (LIB_VCarriers.eta a.challenges) q))
 nci_step h (NNX_Masked.extra extra)
 nci_step h (LIB_VField.qadd_exact (LIB_VField.qadd (LIB_VField.maskValue (LIB_VClaims.value a.prefix_) r.2.1)
  (LIB_VField.qmul (LIB_VCarriers.eta a.challenges) q)) (LIB_VCarriers.at28 extra))
 -- gate
 obtain ⟨b, hb, h⟩ := bindInv h
 cases b
 rotate_left; nci_kill h
 have gate := toRawInj _ _ (qmNeFalse _ _ hb)
 nci_nrh h
 -- state before z0
 nci_step h (LIB_VRecords.state_exact (LIB_VCode.digest env) r.2.2)
 -- first circle
 obtain ⟨⟨z0 | _, t2⟩, h10, h⟩ := bindInv h; rotate_left; nci_kill h
 have hc0 := NOC_ConvSemantic.circle NOC_FinishSource.Bi r.2.2 rec25 env z0 t2 h10
 nci_nrh h
 -- record 26, decode, second circle
 obtain ⟨rec26 | _, h7, h⟩ := bindInv h; rotate_left; nci_kill h
 have hrec26 := NOC_ConvSemantic.record a.prefix_ 26#u8 rec26 h7
 nci_nrh h
 obtain ⟨braw | _, h8, h⟩ := bindInv h; rotate_left; nci_kill h
 obtain ⟨beforeZ1, hbefore, hbraw⟩ := NOC_ConvSemantic.decode rec26 0#usize
  (NNV_FinishDecodeDomains.before a.prefix_ rec26 hrec26) braw h8
 subst hbraw
 nci_nrh h
 obtain ⟨⟨z1 | _, t3⟩, h11, h⟩ := bindInv h; rotate_left; nci_kill h
 have hc1 := NOC_ConvSemantic.circle NOC_FinishSource.Bi t2 rec26 env z1 t3 h11
 nci_nrh h
 -- distinct points
 obtain ⟨b2, hb2, h⟩ := bindInv h
 cases b2
 rotate_left; nci_kill h
 have hne := pointNe _ _ hb2
 nci_nrh h
 -- row-2 payload and root copy
 obtain ⟨raw2 | _, h13, h⟩ := bindInv h; rotate_left; nci_kill h
 have hpay := NOC_ConvSemantic.payload a.prefix_ 2#u8 raw2 h13
 nci_nrh h
 obtain ⟨tr2, h14, h⟩ := bindInv h
 obtain ⟨a3, hu, h⟩ := bindInv h
 cases tr2 with
 | Err e => nci_kill hu
 | Ok arr =>
  obtain ⟨root1, hroot⟩ := rootConv raw2 arr h14
  refine ⟨?v, ?_⟩
  rotate_left
  unfold NNH_FinishReturns.value
  refine (bvStep hr).trans ?_
  refine (bvStep cl.1).trans ?_
  refine (bvStep (mapEOk _ hq)).trans ?_
  refine (bvStep hrec25).trans ?_
  refine (bvStep hextra).trans ?_
  refine (bvStep (gateOk _ gate)).trans ?_
  refine (bvStep hrec25).trans ?_
  refine (bvStep hc0).trans ?_
  refine (bvStep hrec26).trans ?_
  refine (bvStep hbefore).trans ?_
  refine (bvStep hrec26).trans ?_
  refine (bvStep hc1).trans ?_
  refine (bvStep (distinctOk _ hne)).trans ?_
  refine (bvStep hpay).trans ?_
  simp only [hroot] <;> rfl

/-- Converse of NOC_Op9.op9 (X3): an Ok installed op9 at the host configuration,
on a granted reservation and a validated public digest, gives an ok returned
library observed value. -/
theorem op9 {W Tx : Type} (c : NNH_HostCtx.Ctx W Tx) (pub : NNH_Libraries.VL.Public) (bytes : Slice U8)
 (granted : (NNH_Run5bCtx.envOf c).reservation = true)
 (digest : LIB_VPublicDomain.publicDigestDom pub)
 (called : ∃ s, (DrvC_Installation.currentInstalled (NNH_Run5bCtx.configuration c)).op9
   (NNV_PreparedAtHost.digest c) (AspisR1CurrentCaller.FirstComposition.toCurrentPublic pub) bytes () none =
   .ok (.Ok s)) :
 ∃ sem, NNH_ObservedReturns.value ⟨pub, LIB_Carriers.bytes bytes⟩ (NNH_Run5bCtx.envOf c) = .ok sem := by
 obtain ⟨s, h⟩ := called
 rw [NOC_Op9Slot.slot c, NOC_Op9Slot.reservation c granted] at h
 unfold AspisR1CurrentCaller.S1SemanticInstallation.verify at h
 rw [NOC_Op9Slot.pub_round, NOC_Op9Slot.digest c] at h
 obtain ⟨res | _, hv, h⟩ := bindInv h; rotate_left; nci_kill h
 unfold AspisR1PublicPreparation.VerifyPrefix.verify at hv
 nci_nrh hv
 obtain ⟨pre | _, h1, hv⟩ := bindInv hv; rotate_left; nci_kill hv
 obtain ⟨pfx, hp, hpre⟩ := NOC_ConvSemantic.parse bytes (NNH_Run5bCtx.envOf c) pre h1
 subst hpre
 nci_nrh hv
 obtain ⟨t | _, h2, hv⟩ := bindInv hv; rotate_left; nci_kill hv
 have hk : LIB_Env.nativeKey (LIB_VCarriers.c1Root pfx) = (LIB_VCarriers.prefixRaw pfx).c1_root :=
  NNX_RootCopy.key _
 have htr : LIB_VLib.publicTranscriptValue (pub,LIB_VCarriers.c1Root pfx) (NNH_Run5bCtx.envOf c) = .ok t := by
  apply NOC_ConvSemantic.transcript
  first
   | (rw [hk]; exact h2)
   | (simp only [hk]; exact h2)
   | exact hk ▸ h2
 nci_nrh hv
 obtain ⟨⟨cs | _, after⟩, h3, hv⟩ := bindInv hv; rotate_left; nci_kill hv
 obtain ⟨ch, hb, hcs⟩ := NOC_ConvSemantic.begin_ (pfx,t) (NNH_Run5bCtx.envOf c) cs after h3
 subst hcs
 nci_nrh hv
 obtain ⟨sem, hfin⟩ := finish ⟨pub,pfx,after,ch⟩ (NNH_Run5bCtx.envOf c) granted digest _ t htr ⟨res, hv⟩
 refine ⟨sem, ?_⟩
 unfold NNH_ObservedReturns.value
 refine (bvStep hp).trans ?_
 refine (bvStep htr).trans ?_
 refine (bvStep hb).trans ?_
 exact hfin

#print axioms bindInv
#print axioms stepInv
#print axioms bvStep
#print axioms mapEOk
#print axioms ifOk
#print axioms gateOk
#print axioms distinctOk
#print axioms toRawInj
#print axioms qmNeFalse
#print axioms pointRefl
#print axioms pointNe
#print axioms tryLen
#print axioms rootConv
#print axioms finish
#print axioms op9
end AspisR1.NOC_SemConv
end
