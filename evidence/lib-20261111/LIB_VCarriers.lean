import LIB_VScalarCarriers
import NMP_prepare.Funs
set_option autoImplicit false
noncomputable section
namespace LIB_VCarriers
open Aeneas Aeneas.Std
abbrev QM31 := LIB_VScalarCarriers.QM31
abbrev Public := AspisR1PublicPreparation.pool_v1.pair_forest_semantic_terminal.r0.Public
/-- A parsed carrier retains the exact source bytes and the actual parse arm.
The constructor is built only in parsePrefix's returned-Ok branch. -/
structure Prefix where
 source : Slice U8
 parsed : AspisR1PrefixAggregateParser.r1_wire.Prefix
 parse_eq : AspisR1PrefixAggregateParser.r1_wire.Prefix.parse source = .ok (.Ok parsed)
def prefixRaw (p : Prefix) : AspisR1PublicPreparation.r1_wire.Prefix :=
 AspisR1PublicPreparation.PrefixAdapter.fromOld p.parsed
abbrev Transcript := AspisR1PublicPreparation.r1_wire.SemanticTranscript Unit
abbrev Alpha := Array QM31 10#usize
abbrev Claims := Array (Array QM31 29#usize) 3#usize
abbrev K29 := Array QM31 29#usize
/-- Canonical challenges are represented once; the original challenge literal
copies these SAME six source fields. -/
structure Challenges where
 lambda : QM31
 chi : QM31
 theta : QM31
 zc : Alpha
 mu : QM31
 eta : QM31
abbrev OrigChallenges := Challenges
abbrev Point := AspisR1PublicPreparation.aspis_core.circle.SecureCirclePoint
abbrev Record := AspisR1PublicPreparation.r1_wire.ValidatedRecord
abbrev WErr := AspisR1PublicPreparation.r1_wire.Error
abbrev VErr := LIB_ErrorDebug.VErr
abbrev CodecErr := NMP_prepare.compact.CodecError
abbrev View := AspisR1PublicPreparation.verifier.View
abbrev Prepared := AspisR1PublicPreparation.verifier.Prepared
abbrev E29 := Array AspisR1PublicPreparation.aspis_core.field.WideExact 29#usize
abbrev Acc := AspisR1PublicPreparation.verifier.Accumulator
abbrev Geo := AspisR1Stage2.verifier.QueryGeometry
abbrev Weights := AspisR1Stage2.verifier.BatchedWeights
abbrev qDec := LIB_VScalarCarriers.qDec
def pDec : DecidableEq Point := Classical.decEq _
def wTerminal : WErr := .Terminal
def wEqualCirclePoints : WErr := .EqualCirclePoints
def wPublic : WErr := .Public
def vParse : VErr := .Parse
def vSemantic : VErr := .Semantic
def vAllocation : VErr := .Allocation
def codecToV (_ : CodecErr) : VErr := vParse
abbrev debugV := LIB_ErrorDebug.debug
def alphaRaw (a : Alpha) : Array LIB_VScalarCarriers.RawQ 10#usize :=
 LIB_VScalarCarriers.array LIB_VScalarCarriers.toRaw a
def k29Raw (a : K29) : Array LIB_VScalarCarriers.RawQ 29#usize :=
 LIB_VScalarCarriers.array LIB_VScalarCarriers.toRaw a
def claimsRaw (a : Claims) : Array (Array LIB_VScalarCarriers.RawQ 29#usize) 3#usize :=
 LIB_VScalarCarriers.array k29Raw a
def challengesRaw (c : Challenges) : AspisR1PublicPreparation.r1_wire.Challenges :=
 ⟨LIB_VScalarCarriers.toRaw c.lambda,LIB_VScalarCarriers.toRaw c.chi,
  LIB_VScalarCarriers.toRaw c.theta,alphaRaw c.zc,
  LIB_VScalarCarriers.toRaw c.mu,LIB_VScalarCarriers.toRaw c.eta⟩
def origChallenges (c : Challenges) : OrigChallenges :=
 ⟨c.lambda,c.chi,c.theta,c.zc,c.mu,c.eta⟩
def eta (c : Challenges) : QM31 := c.eta
def at28 (a : K29) : QM31 := a.val[28]'(by
 have h := a.property
 change a.val.length = 29 at h
 omega)
def c1Root (p : Prefix) : RSL.B32 := LIB_Carriers.b32 p.parsed.c1_root
def state (t : Transcript) : RSL.B32 := LIB_Carriers.b32 t.state
def viewSemantic (v : View) : RSL.Bytes := LIB_Carriers.bytes v.semantic
def zeroE29 : E29 := Array.repeat 29#usize AspisR1PublicPreparation.aspis_core.field.WideExact.ZERO
/-- Emitted From<CodecError>, frozen candidate.rs:22, no dictionary or premise. -/
theorem codec_native (e : CodecErr) :
 NMP_prepare.verifier.Error.Insts.CoreConvertFromCodecError.from e = .ok .Parse := rfl
theorem codec_exact (e : CodecErr) : codecToV e = vParse := rfl
theorem prefix_source (p : Prefix) :
 AspisR1PrefixAggregateParser.r1_wire.Prefix.parse p.source = .ok (.Ok p.parsed) := p.parse_eq
theorem prefix_fields (p : Prefix) :
 (prefixRaw p).c1_root = p.parsed.c1_root ∧ (prefixRaw p).records = p.parsed.records := ⟨rfl,rfl⟩
theorem eta_raw (c : Challenges) :
 (challengesRaw c).eta = LIB_VScalarCarriers.toRaw (eta c) := rfl
theorem orig_raw (c : Challenges) : challengesRaw (origChallenges c) = challengesRaw c := rfl
theorem state_exact (t : Transcript) : (state t).bytes = LIB_Carriers.bytes (Array.to_slice t.state) := rfl
theorem c1Root_exact (p : Prefix) :
 (c1Root p).bytes = LIB_Carriers.bytes (Array.to_slice (prefixRaw p).c1_root) := rfl
theorem viewSemantic_exact (v : View) : viewSemantic v = LIB_Carriers.bytes v.semantic := rfl
theorem zeroE29_exact :
 zeroE29 = Array.repeat 29#usize AspisR1PublicPreparation.aspis_core.field.WideExact.ZERO := rfl
#print axioms codec_native
#print axioms codec_exact
#print axioms prefix_source
#print axioms prefix_fields
#print axioms eta_raw
#print axioms orig_raw
#print axioms state_exact
#print axioms c1Root_exact
#print axioms viewSemantic_exact
#print axioms zeroE29_exact
end LIB_VCarriers
