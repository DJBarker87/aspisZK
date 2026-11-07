import NNG_Data137
import NMP_Install138
import NNG_EmittedCallGraph
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_Parse137
open Aeneas Aeneas.Std Result NMP_prepare NMP_Transport
open NMP_ResultTransport (outer inner)

def raise (reply : Except LIB_VCarriers.WErr LIB_VCarriers.Prefix) : core.result.Result r1_wire.Prefix r1_wire.Error :=
 match reply with
 | .ok p=>.Ok (fromT13 (LIB_VCarriers.prefixRaw p))
 | .error e=>.Err (fromT12 e)

theorem raw (source : Slice U8) : NMP_Install138.parse source = outer raise (LIB_VParsePrefix.model (LIB_Carriers.bytes source)) := by
  have model : NGX_PrefixCarrier.result (AspisR1PrefixAggregateParser.r1_wire.Prefix.parse source) =
      (do let out←LIB_VParsePrefix.model (LIB_Carriers.bytes source);Result.ok (LIB_VParsePrefix.forget out)) := by
    rw [LIB_VParsePrefix.model_same]
    exact (LIB_VParsePrefix.raw_exact source).symm
  unfold NMP_Install138.parse
  rw [model]
  generalize LIB_VParsePrefix.model (LIB_Carriers.bytes source) = reply
  cases reply with
  | fail e=>rfl
  | div=>rfl
  | ok out=>cases out <;> rfl
#print axioms raw

def decode (a : NNG_Data137.Args) : core.result.Result r1_wire.Prefix r1_wire.Error → Except LIB_VCarriers.WErr LIB_VCarriers.Prefix
 | .Err e=>.error (toT12 e)
 | .Ok _=>LIB_VParsePrefix.eval a.bytes

theorem projected (a : NNG_Data137.Args) (domain : RSL.TX1_137.Domain NNG_Data137.VL a) :
    NNG_EmittedCallGraph.resultMap (decode a) (NMP_Install138.parse (NNG_Data137.bytes a.bytes)) =
      LIB_VParsePrefix.model a.bytes := by
  rw [raw,NNG_Data137.bytes_exact a domain]
  cases h : LIB_VParsePrefix.model a.bytes with
  | fail e=>rfl
  | div=>rfl
  | ok out=>
    cases out with
    | error e=>simp only [outer,raise,decode,NNG_EmittedCallGraph.resultMap,fromT12_inverse]
    | ok p=>simp only [outer,raise,decode,LIB_VParsePrefix.eval,h,LIB_VResult.value,NNG_EmittedCallGraph.resultMap,id_eq]
#print axioms projected
theorem succeeded (source : Slice U8) (parsed : r1_wire.Prefix)
    (success : NMP_Install138.parse source = .ok (.Ok parsed)) :
    ∃ p : LIB_VCarriers.Prefix,LIB_VParsePrefix.model (LIB_Carriers.bytes source)=.ok (.ok p) ∧
      parsed=fromT13 (LIB_VCarriers.prefixRaw p) := by
  have actual := raw source
  rw [success] at actual
  cases h : LIB_VParsePrefix.model (LIB_Carriers.bytes source) with
  | fail e=>simp only [h,outer] at actual;cases actual
  | div=>simp only [h,outer] at actual;cases actual
  | ok out=>
    cases out with
    | error e=>simp only [h,outer,raise] at actual;cases actual
    | ok p=>
      refine ⟨p,h,?_⟩
      exact core.result.Result.Ok.inj (Result.ok.inj actual)
#print axioms succeeded
end AspisR1.NNG_Parse137
