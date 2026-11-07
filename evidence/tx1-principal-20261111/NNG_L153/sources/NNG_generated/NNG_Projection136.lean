import NNG_Array136
import NNG_Root32
import NNG_Equality136
import RSL_TX1_136
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_Projection136
open Aeneas Aeneas.Std Result NNG_verify_finish NNG_Emitted NNG_Array136

/-- Carrier maps and inlined data-field laws only. This is NOT a VLib
instance and defines none of its CLOSED operation fields. LIB supplies it. -/
structure Representation (VL : RSL.VLib) (H : Type) where
  publicValue : Public → VL.Public
  prefixValue : r1_wire.Prefix → VL.Prefix
  transcript : r1_wire.SemanticTranscript H → VL.Transcript
  challenges : aspis_core.state_only_prefix.r0.Challenges → VL.Challenges
  original : aspis_core.state_only_prefix.r0.Challenges → VL.OrigChallenges
  q : Q → VL.QM31
  alpha : Alpha → VL.Alpha
  claims : Claims → VL.Claims
  k29 : K29 → VL.K29
  point : aspis_core.circle.SecureCirclePoint → VL.Point
  record : r1_wire.ValidatedRecord → VL.Record
  error : r1_wire.Error → VL.WErr
  bytes : Slice U8 → RSL.Bytes
  b32 : Array U8 32#usize → RSL.B32
  q_injective : Function.Injective q
  point_injective : Function.Injective point
  publicError : error r1_wire.Error.Public = VL.wPublic
  terminalError : error r1_wire.Error.Terminal = VL.wTerminal
  equalError : error r1_wire.Error.EqualCirclePoints = VL.wEqualCirclePoints
  orig : ∀ c, VL.origChallenges (challenges c) = original c
  eta : ∀ c, VL.eta (challenges c) = q c.eta
  at28 : ∀ a, VL.at28 (k29 a) = q (get a 28#usize (by decide))
  c1Root : ∀ p, VL.c1Root (prefixValue p) = b32 p.c1_root
  bytes_length : ∀ s, (bytes s).length = s.val.length
  root_bytes : ∀ (s : Slice U8) (h : s.val.length = 32),
    (b32 (NNG_Root32.value s h)).bytes = bytes s

def args {VL : RSL.VLib} {H W : Type} (p : Representation VL H) (s : Parent H W) :
    RSL.TX1_136.Args VL :=
  ⟨p.publicValue s.publicValue,p.prefixValue s.prefixValue,p.transcript s.transcript,p.challenges s.challenges⟩

def verified {VL : RSL.VLib} {H : Type} (p : Representation VL H)
    (v : r1_semantic.Verified H) : RSL.Verified VL :=
  { roots := (p.b32 (get v.roots 0#usize (by decide)),p.b32 (get v.roots 1#usize (by decide))),
    challenges := p.challenges v.challenges, alpha := p.alpha v.alpha, claims := p.claims v.claims,
    extra := p.k29 v.extra, before_z1 := p.k29 v.before_z1, state_before_z0 := p.b32 v.state_before_z0,
    z := (p.point (get v.z 0#usize (by decide)),p.point (get v.z 1#usize (by decide))),
    transcript := p.transcript v.transcript }

def output {VL : RSL.VLib} {H : Type} (p : Representation VL H) :
    Output H → Except VL.WErr (RSL.Verified VL)
  | .Ok v => .ok (verified p v)
  | .Err e => .error (p.error e)

def rounds {VL : RSL.VLib} {H : Type} (p : Representation VL H) :
    core.result.Result (Q × Alpha × r1_wire.SemanticTranscript H) r1_wire.Error →
      Except VL.WErr (VL.QM31 × VL.Alpha × VL.Transcript)
  | .Ok r => .ok (p.q r.1,p.alpha r.2.1,p.transcript r.2.2)
  | .Err e => .error (p.error e)

def claimsReply {VL : RSL.VLib} {H : Type} (p : Representation VL H) :
    core.result.Result Claims r1_wire.Error → Except VL.WErr VL.Claims
  | .Ok c => .ok (p.claims c)
  | .Err e => .error (p.error e)

def terminalReply {VL : RSL.VLib} {H : Type} (p : Representation VL H) :
    core.result.Result Q aspis_core.state_only_prefix.r0.Error → Except Unit VL.QM31
  | .Ok q => .ok (p.q q)
  | .Err _ => .error ()

def recordReply {VL : RSL.VLib} {H : Type} (p : Representation VL H) :
    core.result.Result r1_wire.ValidatedRecord r1_wire.Error → Except VL.WErr VL.Record
  | .Ok r => .ok (p.record r)
  | .Err e => .error (p.error e)

def decodeReply {VL : RSL.VLib} {H : Type} (p : Representation VL H) :
    core.result.Result K29 r1_wire.Error → Except VL.WErr VL.K29
  | .Ok r => .ok (p.k29 r)
  | .Err e => .error (p.error e)

def circleReply {VL : RSL.VLib} {H : Type} (p : Representation VL H)
    (r : core.result.Result aspis_core.circle.SecureCirclePoint r1_wire.Error × r1_wire.SemanticTranscript H) :
    Except VL.WErr (VL.Point × VL.Transcript) :=
  match r.1 with
  | .Ok z => .ok (p.point z,p.transcript r.2)
  | .Err e => .error (p.error e)

def payloadReply {VL : RSL.VLib} {H : Type} (p : Representation VL H) :
    core.result.Result (Slice U8) r1_wire.Error → Except VL.WErr RSL.Bytes
  | .Ok r => .ok (p.bytes r)
  | .Err e => .error (p.error e)
end AspisR1.NNG_Projection136
