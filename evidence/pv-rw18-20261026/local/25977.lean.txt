import R1Z.ProverRw18FieldEncode
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverRw18FullCarrier
open Aeneas Aeneas.Std ProverRw18FieldMeaning

def raw (x : Q) : Raw := ⟨⟨x.c0.a,x.c0.b⟩,⟨x.c1.a,x.c1.b⟩⟩
def value (x : Q) : K := decode (raw x)
def canonical (x : Q) : Prop := Canonical (raw x)
def encode (x : K) : Q := full (ProverRw18FieldEncode.encode x)

theorem raw_full (x : Raw) : raw (full x)=x := by
  rcases x with ⟨⟨a,b⟩,⟨c,d⟩⟩;rfl
theorem full_raw (x : Q) : full (raw x)=x := by
  rcases x with ⟨⟨a,b⟩,⟨c,d⟩⟩;rfl
theorem value_encode (x : K) : value (encode x)=x := by
  unfold value encode
  rw [raw_full,ProverRw18FieldEncode.decoded]
theorem canonical_encode (x : K) : canonical (encode x) := by
  unfold canonical encode
  rw [raw_full]
  exact ProverRw18FieldEncode.canonical x
theorem encode_value (x : Q) (hx : canonical x) : encode (value x)=x := by
  unfold encode value
  rw [ProverRw18FieldEncode.encoded _ hx,full_raw]
theorem value_injective (x y : Q) (hx : canonical x) (hy : canonical y) (same : value x=value y) : x=y := by
  rw [← encode_value x hx,← encode_value y hy,same]

#print axioms raw_full
#print axioms full_raw
#print axioms value_encode
#print axioms canonical_encode
#print axioms encode_value
#print axioms value_injective
end R1Z.ProverRw18FullCarrier
