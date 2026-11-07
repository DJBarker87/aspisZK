import LIB_Bytes
import LIB_VResult
import NGX_PrefixCarrier
set_option autoImplicit false
noncomputable section
namespace LIB_VParsePrefix
open Aeneas Aeneas.Std LIB_VCarriers
open AspisR1
abbrev Parser := AspisR1PrefixAggregateParser.r1_wire.Prefix
/-- The exact successful constructor carries the SAME original byte borrow. -/
def parseRaw (source : Slice U8) : Result (Except WErr Prefix) :=
 match h : AspisR1PrefixAggregateParser.r1_wire.Prefix.parse source with
 | .ok (.Ok p) => .ok (.ok ⟨source,p,h⟩)
 | .ok (.Err e) => .ok (.error (NGX_PrefixCarrier.error e))
 | .fail e => .fail e
 | .div => .div
def forget : Except WErr Prefix → core.result.Result AspisR1PublicPreparation.r1_wire.Prefix WErr
 | .ok p => .Ok (prefixRaw p)
 | .error e => .Err e
theorem raw_exact (source : Slice U8) :
 (do let out ← parseRaw source;Result.ok (forget out)) =
 NGX_PrefixCarrier.result (AspisR1PrefixAggregateParser.r1_wire.Prefix.parse source) := by
 unfold parseRaw
 split <;> rfl
/-- CLOSED TX1:138 byte-borrow bound, with no accepted-parser premise. -/
def semanticBytesDom (b : RSL.Bytes) : Prop := b.length≤57607
def model (b : RSL.Bytes) : Result (Except WErr Prefix) := by
 classical
 exact if h : b.length≤Usize.max then parseRaw (LIB_Bytes.fromBytes b h)
 else .fail .arrayOutOfBounds
def parsePrefix : RSL.Child RSL.Bytes (Except WErr Prefix) :=
 ⟨semanticBytesDom,fun b=>LIB_Carriers.resultGraph id (fun _=>model b) (fun _=>[])⟩
theorem model_same (source : Slice U8) : model (LIB_Carriers.bytes source) = parseRaw source := by
 classical
 simp only [model,dif_pos (LIB_Bytes.bytes_bound source),LIB_Bytes.from_bytes]
theorem law_exact (b : RSL.Bytes) (env : RSL.Env) (o : RSL.Obs (Except WErr Prefix)) :
 parsePrefix.law b env o ↔ o=LIB_Carriers.resultObs id [] (model b) := Iff.rfl
def eval (b : RSL.Bytes) : Except WErr Prefix :=
 LIB_VResult.value id (.error (.Length 0#u8)) (model b)
theorem returns (b : RSL.Bytes) (env : RSL.Env) :
 NND_Returned.Returns (parsePrefix.law b) env (eval b) :=
 LIB_VResult.returns id (.error (.Length 0#u8)) _ _ env
theorem functional : RSL.Child.Functional parsePrefix :=
 fun b _ => LIB_VResult.functional id _ _
#print axioms raw_exact
#print axioms model_same
#print axioms law_exact
#print axioms returns
#print axioms functional
end LIB_VParsePrefix
