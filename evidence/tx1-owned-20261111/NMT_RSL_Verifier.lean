/-
RSL_Verifier: generic-error Result layer, the `Child` packet shape, and the
CLOSED-child interface of the verifier-crate rows TX1:136/137/087/094 and
TX1:328.

`Child A B` is how every CLOSED child enters a parent reference: its (bf)(2)
own-argument domain `dom` (the conjunction of that child's ledger caller
clauses, verbatim) and its complete law `law` (all arms, ordered events, abort
prefixes).  `Child.run` requires `dom` at the SAME argument, so a parent
RowSpec is provable only if the parent discharges every child caller clause
from its own domain and earlier child laws.  Each field of `VLib` names the
one CLOSED root that instantiates it; the gate checks this clause by clause.
Instantiating `dom` with anything weaker than the child's recorded clauses, or
`law` with anything weaker than its proved statement, is a gate finding.
-/
import NMT_RSL_Base
set_option autoImplicit false

namespace RSL

/-! ## Generic `Result<α, ε>` layer -/

def RE (ε α : Type) : Type := Spec (Except ε α)

namespace RE
def pure {ε α : Type} (a : α) : RE ε α := Spec.pure (.ok a)
def throw {ε α : Type} (e : ε) : RE ε α := Spec.pure (.error e)
def bind {ε α β : Type} (m : RE ε α) (k : α → RE ε β) : RE ε β :=
  Spec.bind m (fun r => match r with
    | .ok a => k a
    | .error e => Spec.pure (.error e))
def seq {ε β : Type} (m : RE ε Unit) (k : RE ε β) : RE ε β := bind m (fun _ => k)
def lift {ε α : Type} (m : Spec α) : RE ε α := Spec.map Except.ok m
def ofExcept {ε α : Type} (x : Except ε α) : RE ε α := Spec.pure x
def check {ε : Type} (bad : Bool) (e : ε) : RE ε Unit := if bad then throw e else pure ()
/-- `?` through `From`/`map_err`. -/
def mapE {ε ε' α : Type} (f : ε → ε') (r : Except ε α) : Except ε' α :=
  match r with | .ok a => .ok a | .error e => .error (f e)
def mapErr {ε ε' α : Type} (f : ε → ε') (m : RE ε α) : RE ε' α :=
  Spec.map (mapE f) m

theorem bind_throw {ε α β : Type} (e : ε) (k : α → RE ε β) :
    RE.bind (RE.throw e) k = RE.throw e := by
  unfold RE.bind RE.throw; rw [Spec.bind_pure]
theorem bind_pure {ε α β : Type} (a : α) (k : α → RE ε β) :
    RE.bind (RE.pure a) k = k a := by
  unfold RE.bind RE.pure; rw [Spec.bind_pure]
theorem seq_throw {ε β : Type} (e : ε) (k : RE ε β) : RE.seq (RE.throw e) k = RE.throw e :=
  bind_throw e _
theorem seq_pure {ε β : Type} (k : RE ε β) : RE.seq (RE.pure ()) k = k := bind_pure () _
theorem check_true {ε : Type} (e : ε) : RE.check true e = (RE.throw e : RE ε Unit) := rfl
theorem check_false {ε : Type} (e : ε) : RE.check false e = (RE.pure () : RE ε Unit) := rfl
end RE

/-! ## Child packets -/

structure Child (A B : Type) where
  dom : A → Prop
  law : A → Spec B

def Child.run {A B : Type} (c : Child A B) (a : A) : Spec B := Spec.call c.dom c.law a


theorem Child.run_det {A B : Type} (c : Child A B) (a : A) (env : Env) (x : B)
    (hd : c.dom a) (hl : ∀ o, c.law a env o ↔ o = ⟨.ret x, []⟩) (o : Obs B) :
    c.run a env o ↔ o = ⟨.ret x, []⟩ :=
  ⟨fun h => (hl o).mp h.2, fun h => ⟨hd, (hl o).mpr h⟩⟩

theorem RE.mapErr_det {ε ε' α : Type} (f : ε → ε') (m : RE ε α) (env : Env) (r : Except ε α)
    (hm : ∀ o, m env o ↔ o = ⟨.ret r, []⟩) (o : Obs (Except ε' α)) :
    RE.mapErr f m env o ↔ o = ⟨.ret (RE.mapE f r), []⟩ := by
  unfold RE.mapErr Spec.map
  rw [Spec.bind_det _ _ env r hm]
  rfl

theorem RE.bind_err_det {ε α β : Type} (m : RE ε α) (k : α → RE ε β) (env : Env) (e : ε)
    (hm : ∀ o, m env o ↔ o = ⟨.ret (.error e), []⟩) (o : Obs (Except ε β)) :
    RE.bind m k env o ↔ o = ⟨.ret (.error e), []⟩ := by
  unfold RE.bind
  rw [Spec.bind_det _ _ env (.error e) hm]
  rfl

/-! ## Verifier-crate interface -/

/-- `verifier::Observer = Option<fn(Phase)>`: a function-pointer identity.
Every deployed caller passes `observer()` = None (CLOSED TX1:329/TX2:212), and
under ruling (al) the rows are certified at that instantiation: `obs = none`
is a (bf)(2) own-input clause of TX1:087/094/328. -/
structure PhaseFn where
  id : Nat
abbrev Observer := Option PhaseFn

/-- Compact proof layout (compact.rs:25-69). -/
def OFF_SEMANTIC : Nat := 16
def OFF_Y1 : Nat := 7031
def OFF_INACTIVE : Nat := 7495
def OFF_ROUND0 : Nat := 7527
def OFF_FOLDED_ROOT : Nat := 7751
def OFF_ROUND1 : Nat := 7783
def LOGICAL_SEMANTIC : Nat := 13831
def LOGICAL_Y1 : Nat := 928
def SPLIT : Nat := 10
def VPROOF_BYTES : Nat := 57607

structure VLib where
  -- carriers (opaque; values flow through unchanged)
  Public : Type          -- pair_forest_semantic_terminal::r0::Public<'_>
  Prefix : Type          -- r1_wire::Prefix<'_>
  Transcript : Type      -- SemanticTranscript<SolanaDigest>
  Challenges : Type      -- r1_wire::Challenges
  OrigChallenges : Type  -- state_only_prefix::r0::Challenges
  QM31 : Type
  Alpha : Type           -- [QM31; 10]
  Claims : Type          -- Box<[[QM31; 29]; 3]>
  K29 : Type             -- [QM31; 29]
  Point : Type           -- SecureCirclePoint
  Record : Type          -- r1_wire::ValidatedRecord<'_>
  WErr : Type            -- r1_wire::Error
  VErr : Type            -- verifier::Error
  CodecErr : Type        -- compact::CodecError
  View : Type            -- verifier::View<'_>
  Prepared : Type        -- verifier::Prepared (boxed by Prepared::new)
  E29 : Type             -- [E; 29]
  Acc : Type             -- verifier::Accumulator
  Geo : Type             -- verifier::QueryGeometry
  Weights : Type         -- verifier::BatchedWeights
  [qDec : DecidableEq QM31]
  [pDec : DecidableEq Point]
  -- error constructors used by the bodies
  wTerminal : WErr
  wEqualCirclePoints : WErr
  wPublic : WErr
  vParse : VErr
  vSemantic : VErr
  vAllocation : VErr
  /-- `impl From<CodecError> for Error` (candidate.rs:22): every codec error is Parse. -/
  codecToV : CodecErr → VErr
  -- `format!("{:?}", e)` for verifier::Error: the payload of lib.rs::error's log
  -- line (CLOSED TX1:NGB001 / TX2:211, NIS_ErrorJoin)
  debugV : VErr → String
  -- own-input domain of verify_finish (TX1:136): the (bf)(2) clauses that its
  -- children place on 136's OWN arguments and that 136 cannot discharge
  -- internally, verbatim from the ledger records NJW/NKN/NLS_explicit_child_domains
  -- (e.g. NLS-bf:TX1:136:TX1:256:hd `NKR_DigestChildren.Domain (NKR_TermPublic.value pub)`,
  -- NJW-caller:TX1:136:TX1:134 same valid Prefix / transcript carry).  Arguments:
  -- public, prefix, transcript, challenges.
  finishInputDom : Public → Prefix → Transcript → Challenges → Prop
  -- the part of the domain that concerns `public` alone and so propagates
  -- unchanged up the chain 137 -> 087 -> 094 -> 328 -> 345, where it is
  -- discharged from the decoded, validated statement (NLS-bf:TX1:136:TX1:256:hd)
  publicDom : Public → Prop
  -- TX1:138 Prefix::parse own clause on its byte argument, if its root has one
  -- (TX1:087 discharges it from the expand_semantic law)
  semanticBytesDom : Bytes → Prop
  -- r1_semantic children (TX1:136)
  semanticRounds : Child (Prefix × Transcript) (Except WErr (QM31 × Alpha × Transcript))  -- TX1:134 NJM_InvocationRoots
  claims : Child Prefix (Except WErr Claims)                                               -- TX1:129 NKA_ClaimsRoot
  origChallenges : Challenges → OrigChallenges        -- struct literal, lines 239-246
  terminalQm31 : Child (Public × Claims × Alpha × OrigChallenges) (Except Unit QM31)     -- TX1:256 NLH_WrapperRoot
  maskValue : Claims → Alpha → QM31                   -- TX1:076 NHU_Mask at claims[0][0..16], [16..27], [27]
  validatedRecord : Prefix → Nat → Except WErr Record -- TX1:141 NFU_PrefixRecords
  decodeK29 : Record → Nat → Except WErr K29          -- TX1:147 NGO_CallCases
  eta : Challenges → QM31                             -- field read
  qadd : QM31 → QM31 → QM31                           -- TX1:024
  qmul : QM31 → QM31 → QM31                           -- TX1:029
  at28 : K29 → QM31                                   -- extra[28]
  state : Transcript → B32                            -- TX1:146 NGX_StateImpl
  circle : Child (Transcript × Record) (Except WErr (Point × Transcript))                 -- TX1:142 NJM_InvocationRoots
  payload : Prefix → Nat → Except WErr Bytes          -- TX1:139 NGX_Payload
  c1Root : Prefix → B32                               -- *prefix.c1_root
  -- verify_observed children (TX1:137)
  parsePrefix : Child Bytes (Except WErr Prefix)                                          -- TX1:138 NGX_PrefixCarrier
  publicTranscript : Child (Public × B32) (Except WErr Transcript)                        -- TX1:131 NHG_Lengths
  begin : Child (Prefix × Transcript) (Except WErr (Challenges × Transcript))             -- TX1:150 NGX_BeginDomains
  -- prepare children (TX1:087)
  filled : Child Nat (Except Unit Bytes)              -- TX1:064 heap::filled (Err = allocation failure value)
  expandSemantic : Child (Bytes × Bytes) (Except CodecErr Bytes)   -- TX1:098: (src, dst) -> written dst
  expandValues : Child (Bytes × Bytes) (Except CodecErr Bytes)     -- TX1:099
  wideView : Child (Bytes × Bytes × Bytes) (Except VErr View)      -- TX1:095 NHF_ViewDecoder (proof, semantic, y1)
  viewSemantic : View → Bytes                                      -- v.semantic
  -- tx1 children (TX1:094)
  parseShape : Child Bytes (Except VErr Unit)         -- TX1:086 NJS_Parse
  canonicalScan : Child Bytes (Except VErr Unit)      -- TX1:084 NKL_ScanRoot
  zeroE29 : E29                                        -- [E::ZERO; 29]
  accNew : Child Unit (Except VErr Acc)               -- TX1:174 Accumulator::new(Variant::S2)
  batchMerkle : Child (Bytes × Prepared × B32 × Nat) (Except VErr Unit)  -- TX1:081 NLN_TX1_081
  geometry : Child (Prepared × Nat × Nat) (Except VErr Geo)            -- TX1:181 for_range(&p.queries, lo, hi)
  weightsNew : Child Acc (Except VErr Weights)                         -- TX1:176 BatchedWeights::new(&a.weights)
  queryLoop : Child (Bytes × Prepared × Acc × E29 × Geo × Weights × Nat) (Except VErr (Acc × Weights))  -- TX1:088
  finish : Child (Weights × Acc) Acc                  -- TX1:175 pending.finish(&mut a.weights)
  checkpoint : Child (Prepared × Acc × Bytes × Bytes) Bytes  -- TX1:186 NHS_CheckpointPacket (Vec, abort arm inside)

attribute [instance] VLib.qDec VLib.pDec

/-- `Verified<H>` (r1_semantic.rs:7-23, prover fields off). -/
structure Verified (V : VLib) where
  roots : B32 × B32
  challenges : V.Challenges
  alpha : V.Alpha
  claims : V.Claims
  extra : V.K29
  before_z1 : V.K29
  state_before_z0 : B32
  z : V.Point × V.Point
  transcript : V.Transcript

/-- `Prepared::new(&sem, &v, hash, g)` (CLOSED TX1:179, NHS_PreparedPacket):
writes `g`, returns `Result<Box<Prepared>, Error>`; `g` post on both arms. -/
abbrev PreparedNew (V : VLib) := Child (Verified V × V.View × V.E29) (Except V.VErr V.Prepared × V.E29)

end RSL
