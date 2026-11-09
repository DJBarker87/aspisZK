import NNX_ClaimPorts
import NNX_Comparisons
import NNX_RootCopy
import NNX_FinishDecodePort
import NNV_FinishNativePorts
import LIB_Prepared
set_option autoImplicit false
noncomputable section
namespace AspisR1.NOC_FinishSource
open Aeneas Aeneas.Std Result AspisR1PublicPreparation LIB_VCarriers RSL
abbrev V := NNH_FinishReturns.V

/-- The semantic-finish boundaries installed by the op9 slot at the reserved
configuration: root copy over the Claims-unrolled deployed boundaries. -/
abbrev Bi : FinishModel.Boundaries :=
 AspisR1PublicPreparation.S1SemanticRootCopy.install
  (ClaimsUnrolledFinish.install (NP6_StdModel.calls (.Ok ())) (IDa_Deployed.boundaries (.Ok ())))

/-- One bind of the Result monad, stepped by a full Result equality of its
head. The head is matched up to definitional equality, never by syntax. -/
theorem step {α β : Type} {m : Result α} {v : α} {k : α → Result β} {r : Result β}
 (h : m = .ok v) (rest : k v = r) : (m >>= k) = r := by
 subst h; exact rest

/-- Pure normalization only: Aeneas tuple destructuring, `?` branching on a
known constructor, phase marks and decided Boolean guards. -/
syntax "noc_nrm" : tactic
macro_rules
 | `(tactic| noc_nrm) => `(tactic| ((try simp only [Aeneas.Std.uncurry_apply_pair]);
    (try simp only [Aeneas.Std.uncurry]);
    (try simp only [bind_tc_ok, core.result.Result.Insts.CoreOpsTry.branch, VerifyPrefix.mark,
     Bool.false_eq_true, ↓reduceIte])))
syntax "noc_stp " term : tactic
macro_rules
 | `(tactic| noc_stp $h) => `(tactic| first
    | refine step $h ?_
    | (noc_nrm; refine step $h ?_))

/-- Full fixed finish Result at the installed boundaries, from the SAME
returned finish value. -/
theorem source (a : TX1_136.Args V) (env : Env) (sem : Verified V)
 (called : NNH_FinishReturns.value a env = .ok sem) :
 FinishModel.finish AspisS1ExtractedRoundChildren.children Bi (LIB_VCode.digest env) a.public_
  (prefixRaw a.prefix_) a.transcript (challengesRaw a.challenges) none =
 .ok (.Ok (LIBC_PreparedCarriers.verified LIB_Prepared.types sem)) := by
 obtain ⟨head⟩ := NNV_FinishCut.returned a env sem called
 obtain ⟨tail⟩ := NNV_FinishTail.returned a env sem head
 have rounds := NNV_FinishNativePorts.rounds a.prefix_ a.transcript env head.rounds head.rounded
 have claims := (NNV_FinishClaims.returned a.prefix_ env head.claims head.claimed).2
 have terminalOriginal : LIB_VLib.terminalQm31Value
  (a.public_,head.claims,head.rounds.2.1,V.origChallenges a.challenges) env = .ok tail.terminal := by
  have mapped := tail.terminal_ok
  cases h : LIB_VLib.terminalQm31Value
   (a.public_,head.claims,head.rounds.2.1,V.origChallenges a.challenges) env with
  | error e => rw [h] at mapped;cases mapped
  | ok q =>
   rw [h] at mapped
   exact congrArg Except.ok (Except.ok.inj mapped)
 have terminal := NNV_FinishTerminal.returned _ env tail.terminal terminalOriginal
 have record25 := NNV_FinishRecord.returned a.prefix_ 25#u8 tail.rec25 tail.record25
 have extra := NNX_FinishDecodePort.returned tail.rec25 87#usize tail.extra
  (NNV_FinishDecodeDomains.extra a.prefix_ tail.rec25 tail.record25) tail.decoded25
 have same25 : tail.rec25' = tail.rec25 := Except.ok.inj (tail.record25'.symm.trans tail.record25)
 have circle0 := NNV_FinishNativePorts.circle Bi head.rounds.2.2 tail.rec25' env tail.c0.1 tail.c0.2 tail.circle0
 rw [same25] at circle0
 have record26 := NNV_FinishRecord.returned a.prefix_ 26#u8 tail.rec26 tail.record26
 have before := NNX_FinishDecodePort.returned tail.rec26 0#usize tail.beforeZ1
  (NNV_FinishDecodeDomains.before a.prefix_ tail.rec26 tail.record26) tail.decoded26
 have same26 : tail.rec26' = tail.rec26 := Except.ok.inj (tail.record26'.symm.trans tail.record26)
 have circle1 := NNV_FinishNativePorts.circle Bi tail.c0.2 tail.rec26' env tail.c1.1 tail.c1.2 tail.circle1
 rw [same26] at circle1
 obtain ⟨payload,payloadCall,payloadBytes⟩ := NNX_FinishPayload.source a.prefix_ 2#u8 tail.payload tail.payload_ok
 have converted : TX1_136.toB32 (LIB_Carriers.bytes payload) = some tail.root1 := by
  rw [payloadBytes];exact tail.root_ok
 have rootCall := NNX_RootCopy.source payload tail.root1 converted
 have g16 := NNX_C1Gather.source (LIB_VCode.digest env) head.claims
 have g10 := NNX_Mask10.source (LIB_VCode.digest env) head.claims
 have gate : LIB_VScalarCarriers.toRaw head.rounds.1 = LIB_VScalarCarriers.toRaw
  (LIB_VField.qadd (LIB_VField.qadd (LIB_VField.maskValue head.claims head.rounds.2.1)
   (LIB_VField.qmul (LIB_VCarriers.eta a.challenges) tail.terminal)) (LIB_VCarriers.at28 tail.extra)) :=
  congrArg LIB_VScalarCarriers.toRaw tail.gate
 have neAt : core.cmp.PartialEq.ne.trait_default aspis_core.field.QM31.Insts.CoreCmpPartialEqQM31
  (LIB_VScalarCarriers.toRaw head.rounds.1) (LIB_VScalarCarriers.toRaw
  (LIB_VField.qadd (LIB_VField.qadd (LIB_VField.maskValue head.claims head.rounds.2.1)
   (LIB_VField.qmul (LIB_VCarriers.eta a.challenges) tail.terminal)) (LIB_VCarriers.at28 tail.extra))) =
  .ok false := by
  rw [gate]; exact NNX_Comparisons.qm_ne _
 unfold FinishModel.finish
 noc_stp rounds
 noc_nrm
 noc_stp claims
 noc_nrm
 noc_stp terminal
 noc_stp rfl
 noc_nrm
 noc_stp g16
 noc_stp g10
 noc_stp (NNX_ClaimPorts.row head.claims)
 noc_stp (NNX_ClaimPorts.at27 head.claims)
 noc_stp (LIB_VField.mask_exact head.claims head.rounds.2.1)
 noc_stp record25
 noc_nrm
 noc_stp extra
 noc_nrm
 noc_stp (LIB_VField.qmul_exact (LIB_VCarriers.eta a.challenges) tail.terminal)
 noc_stp (LIB_VField.qadd_exact (LIB_VField.maskValue head.claims head.rounds.2.1)
  (LIB_VField.qmul (LIB_VCarriers.eta a.challenges) tail.terminal))
 noc_stp (NNX_Masked.extra tail.extra)
 noc_stp (LIB_VField.qadd_exact (LIB_VField.qadd (LIB_VField.maskValue head.claims head.rounds.2.1)
  (LIB_VField.qmul (LIB_VCarriers.eta a.challenges) tail.terminal)) (LIB_VCarriers.at28 tail.extra))
 noc_stp neAt
 noc_nrm
 noc_stp (LIB_VRecords.state_exact (LIB_VCode.digest env) head.rounds.2.2)
 noc_nrm
 noc_stp circle0
 noc_nrm
 noc_stp record26
 noc_nrm
 noc_stp before
 noc_nrm
 noc_stp circle1
 noc_nrm
 noc_stp (NNX_Comparisons.point tail.c0.1 tail.c1.1 tail.distinct)
 noc_nrm
 noc_stp payloadCall
 noc_nrm
 noc_stp rootCall
 noc_stp rfl
 have hk : LIB_Env.nativeKey (LIB_VCarriers.c1Root a.prefix_) = (prefixRaw a.prefix_).c1_root :=
  NNX_RootCopy.key _
 have hv := congrArg (LIBC_PreparedCarriers.verified LIB_Prepared.types) tail.semantic
 rw [hv, ← hk]
 rfl
#print axioms step
#print axioms source
end AspisR1.NOC_FinishSource
end
