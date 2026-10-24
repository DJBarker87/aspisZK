import ExtractedSemanticRoundsModel
import AspisR1SemanticCallExtraction.Funs
import AspisR1DecodeKFullV10.Funs
set_option autoImplicit false
namespace AspisS1ExtractedRoundChildren
open Aeneas Aeneas.Std Result
abbrev MainQM := AspisR1PublicPreparation.aspis_core.field.QM31
abbrev GenQM := AspisR1SemanticCallExtraction.aspis_core.field.QM31
abbrev DecodeQM := AspisR1DecodeKFullV10.aspis_core.field.QM31
abbrev DecodeRecord := AspisR1DecodeKFullV10.r1_wire.ValidatedRecord
abbrev DecodeError := AspisR1DecodeKFullV10.r1_wire.Error
abbrev MainRecord := AspisR1PublicPreparation.r1_wire.ValidatedRecord
abbrev MainError := AspisR1PublicPreparation.r1_wire.Error

def recordToDecoder (r : MainRecord) : DecodeRecord := ⟨r.row, r.framed⟩

def decoderQMToMain (q : DecodeQM) : MainQM :=
  ⟨⟨q.c0.a, q.c0.b⟩, ⟨q.c1.a, q.c1.b⟩⟩

def decoderArrayToMain {n : Usize} (a : Array DecodeQM n) : Array MainQM n :=
  ⟨a.val.map decoderQMToMain, by simpa using a.property⟩

def decoderErrorToMain : DecodeError → MainError
  | .Allocation => .Allocation
  | .RowOrder a b => .RowOrder a b
  | .InvalidRow => .InvalidRow
  | .Tag row => .Tag row
  | .Length row => .Length row
  | .NonCanonical row offset => .NonCanonical row offset
  | .Boundary round => .Boundary round
  | .Terminal => .Terminal
  | .EqualCirclePoints => .EqualCirclePoints
  | .TrailingBytes => .TrailingBytes
  | .Public => .Public

def decoderResultToMain (n : Usize) :
    Result (core.result.Result (Array DecodeQM n) DecodeError) →
      Result (core.result.Result (Array MainQM n) MainError)
  | .ok (.Ok a) => .ok (.Ok (decoderArrayToMain a))
  | .ok (.Err e) => .ok (.Err (decoderErrorToMain e))
  | .fail e => .fail e
  | .div => .div

/-- A nominal adapter around the pinned actual indexed decode_k body. -/
def decodeMain (n : Usize) (r : MainRecord) (offset : Usize) :
    Result (core.result.Result (Array MainQM n) MainError) :=
  decoderResultToMain n
    (AspisR1DecodeKFullV10.r1_wire.ValidatedRecord.decode_k n (recordToDecoder r) offset)


def mainToGen (q : MainQM) : GenQM :=
  ⟨⟨q.c0.a, q.c0.b⟩, ⟨q.c1.a, q.c1.b⟩⟩

def genToMain (q : GenQM) : MainQM :=
  ⟨⟨q.c0.a, q.c0.b⟩, ⟨q.c1.a, q.c1.b⟩⟩

def mainArrayToGen (xs : Array MainQM 28#usize) : Array GenQM 28#usize :=
  ⟨xs.val.map mainToGen, by simpa using xs.property⟩

def mainAlphaArrayToGen (xs : Array MainQM 10#usize) : Array GenQM 10#usize :=
  ⟨xs.val.map mainToGen, by simpa using xs.property⟩

def genResultToMain : Result GenQM → Result MainQM
  | .ok q => .ok (genToMain q)
  | .fail e => .fail e
  | .div => .div

def generatedMainBoundary (coefficients : Array MainQM 28#usize) : Result MainQM :=
  genResultToMain (AspisR1SemanticCallExtraction.r1_semantic.semantic_boundary_entry
    (mainArrayToGen coefficients))

def generatedMainValue (coefficients : Array MainQM 28#usize)
    (alpha : Array MainQM 10#usize) (round : Usize) : Result MainQM :=
  genResultToMain (AspisR1SemanticCallExtraction.r1_semantic.semantic_value_entry
    (mainArrayToGen coefficients) (mainAlphaArrayToGen alpha) round)

def generatedRoundBoundaries
    (decodeMain : (N : Usize) → AspisR1PublicPreparation.r1_wire.ValidatedRecord → Usize →
      Result (core.result.Result (Array MainQM N) AspisR1PublicPreparation.r1_wire.Error)) :
    AspisR1PublicPreparation.RoundModel.Boundaries :=
  { decode := decodeMain
    boundary := generatedMainBoundary
    value := generatedMainValue }


/-- Full concrete extracted children. No child function remains a parameter.
Native fold control and parser/Rust/Std/abort interpretation retain their own
source pins and obligations; this definition does not assert that transport. -/
def children : AspisR1PublicPreparation.RoundModel.Boundaries :=
  generatedRoundBoundaries decodeMain

theorem decode_exact (n : Usize) (r : MainRecord) (offset : Usize) :
    children.decode n r offset = decoderResultToMain n
      (AspisR1DecodeKFullV10.r1_wire.ValidatedRecord.decode_k n (recordToDecoder r) offset) := rfl

theorem boundary_exact (p : Array MainQM 28#usize) :
    children.boundary p = genResultToMain
      (AspisR1SemanticCallExtraction.r1_semantic.semantic_boundary_entry (mainArrayToGen p)) := rfl

theorem value_exact (p : Array MainQM 28#usize) (a : Array MainQM 10#usize) (round : Usize) :
    children.value p a round = genResultToMain
      (AspisR1SemanticCallExtraction.r1_semantic.semantic_value_entry
        (mainArrayToGen p) (mainAlphaArrayToGen a) round) := rfl

theorem coordinates_roundtrip (q : MainQM) : genToMain (mainToGen q) = q := by
  cases q with
  | mk c0 c1 => cases c0; cases c1; rfl

theorem preserve_failure (e : Error) :
    genResultToMain (.fail e) = .fail e := rfl

theorem preserve_divergence : genResultToMain .div = .div := rfl

#print axioms decode_exact
#print axioms boundary_exact
#print axioms value_exact
#print axioms coordinates_roundtrip
#print axioms preserve_failure
#print axioms preserve_divergence
end AspisS1ExtractedRoundChildren
