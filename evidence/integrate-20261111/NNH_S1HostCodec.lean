import NNH_S1CodecOk
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNH_S1HostCodec
open Aeneas Aeneas.Std Result _root_.AdapterRw
abbrev Statement := aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1
abbrev FormatError := aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1
abbrev Afterstate := aspis_statement.pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1
abbrev EncodeError := aspis_statement.pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1
/-- Literal missing op21. Returned Ok is the supplied source value. The weak
Err interface permits divergence on rejected values; no error payload is read. -/
def validate (st : Statement) : Result (core.result.Result Unit FormatError) :=
 match NMT_345.validateCall (NNH_S1DecodeOk.carrier st) with
 | .ok (.Ok u) => .ok (.Ok u)
 | .ok (.Err _) => .div
 | .fail e => .fail e
 | .div => .div

def afterCarrier (a : Afterstate) : NMT_345.Afterstate :=
 NMT_345Dec.fromT5 (AspisS6CurrentAdapterCarrier.toPoolV1PairVerifiedAfterstateV1 a)
/-- Literal missing op24 at the SAME afterstate, without an error-value law. -/
def encode (a : Afterstate) : Result (core.result.Result (Array U8 688#usize) EncodeError) :=
 match NMT_345.encodeCall (afterCarrier a) with
 | .ok (.Ok out) => .ok (.Ok out)
 | .ok (.Err _) => .div
 | .fail e => .fail e
 | .div => .div

theorem validate_ok (st : Statement)
 (good : NNH_Libraries.C.validateStatement (NNH_S1DecodeOk.carrier st) = true) :
 validate st = .ok (.Ok ()) := by
 unfold validate
 rw [NNH_S1CodecOk.validate _ good]

theorem encode_ok (a : Afterstate) (out : Array U8 688#usize)
 (called : NMT_345.encodeCall (afterCarrier a) = .ok (.Ok out)) :
 encode a = .ok (.Ok out) := by
 unfold encode
 rw [called]

def install (ops : Ops) : Ops := {ops with op21 := validate,op24 := encode}

#print axioms validate_ok
#print axioms encode_ok
#print axioms install
end AspisR1.NNH_S1HostCodec
end
