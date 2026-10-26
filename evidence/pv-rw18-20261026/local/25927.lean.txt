import R1Z.ProverRw18FieldInjective
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverRw18FieldEncode
open Aeneas Aeneas.Std ProverRw18FieldMeaning
abbrev M := AspisV8R15.ExactTowerBase.M31Exact

-- A direct canonical encoder from field coordinates, independent of the
-- compression implementation or its output. It is a component carrier map,
-- not a whole prover/runtime interpretation.
def word (x : M) : U32 := UScalar.ofNatCore x.val (by
  change x.val<2^32
  have hx : x.val<AspisCircleGroupOrder.P := ZMod.val_lt x
  exact hx.trans (by change (2147483647 : Nat)<4294967296; omega))

theorem word_val (x : M) : (word x).val=x.val := rfl

theorem word_canonical (x : M) : (word x).val<AspisCircleGroupOrder.P := by
  rw [word_val]
  exact ZMod.val_lt x

theorem word_decoded (x : M) : ((word x).val : M)=x := by
  rw [word_val]
  exact ZMod.natCast_zmod_val x

def encode (x : K) : Raw :=
  ⟨⟨word x.re.re,word x.re.im⟩,⟨word x.im.re,word x.im.im⟩⟩

theorem canonical (x : K) : Canonical (encode x) :=
  ⟨⟨word_canonical _,word_canonical _⟩,⟨word_canonical _,word_canonical _⟩⟩

theorem decoded (x : K) : decode (encode x)=x := by
  rcases x with ⟨⟨a,b⟩,⟨c,d⟩⟩
  simp only [encode,decode,AspisR1.ExtractedCurrentQM31Exact.decode,word_decoded]

theorem encoded (x : Raw) (hx : Canonical x) : encode (decode x)=x :=
  ProverRw18FieldInjective.raw _ x (canonical (decode x)) hx (decoded (decode x))

#print axioms word_val
#print axioms word_canonical
#print axioms word_decoded
#print axioms canonical
#print axioms decoded
#print axioms encoded
end R1Z.ProverRw18FieldEncode
