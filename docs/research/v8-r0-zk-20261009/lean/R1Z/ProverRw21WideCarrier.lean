import R1Z.ProverRw18FullCarrier
import R1Z.ProverCommitWideBytes48
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverRw21WideCarrier
open Aeneas Aeneas.Std ProverRwFull
abbrev W := aspis_core.field.wide_exact.WideExact
abbrev E := AspisWideTower.WideExact

def raw (x : W) : ProverCommitWideOps48.Raw :=
  (ProverRw18FullCarrier.raw x.c0,ProverRw18FullCarrier.raw x.c1)

def value (x : W) : E := ProverCommitWideOps48.value (raw x)
def canonical (x : W) : Prop := ProverCommitWideOps48.canonical (raw x)

def encode (x : E) : W := ⟨ProverRw18FullCarrier.encode x.re,ProverRw18FullCarrier.encode x.im⟩

theorem value_encode (x : E) : value (encode x)=x := by
  rcases x with ⟨a,b⟩
  change (⟨ProverRw18FullCarrier.value (ProverRw18FullCarrier.encode a),
    ProverRw18FullCarrier.value (ProverRw18FullCarrier.encode b)⟩ : E)=⟨a,b⟩
  rw [ProverRw18FullCarrier.value_encode,ProverRw18FullCarrier.value_encode]

theorem canonical_encode (x : E) : canonical (encode x) :=
  ⟨ProverRw18FullCarrier.canonical_encode x.re,ProverRw18FullCarrier.canonical_encode x.im⟩

theorem encode_value (x : W) (h : canonical x) : encode (value x)=x := by
  rcases x with ⟨a,b⟩
  change (⟨ProverRw18FullCarrier.encode (ProverRw18FullCarrier.value a),
    ProverRw18FullCarrier.encode (ProverRw18FullCarrier.value b)⟩ : W)=⟨a,b⟩
  rw [ProverRw18FullCarrier.encode_value a h.1,ProverRw18FullCarrier.encode_value b h.2]

theorem injective (x y : W) (hx : canonical x) (hy : canonical y) (h : value x=value y) : x=y := by
  rw [← encode_value x hx,← encode_value y hy,h]

theorem source_cell (x : W) (h : canonical x) :
    ProverCommitWideBytes48.sourceCell (raw x) h=ProverCommitValueRange47.bytes (value x) :=
  ProverCommitWideBytes48.source_image (raw x) h

#print axioms raw
#print axioms value
#print axioms canonical
#print axioms encode
#print axioms value_encode
#print axioms canonical_encode
#print axioms encode_value
#print axioms injective
#print axioms source_cell
end R1Z.ProverRw21WideCarrier
