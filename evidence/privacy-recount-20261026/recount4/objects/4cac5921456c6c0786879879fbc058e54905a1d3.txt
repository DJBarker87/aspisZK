import AspisR1ProducerRelease47.Interpolate48
import R1Z.ProverCommitInverse48
import R1Z.ProverCommitNativeQ48
/-! Four-coordinate source scalar multiplication, for semantic interpolation.
All raw input words are admitted; the actual reducer supplies canonicality. -/
set_option autoImplicit false
namespace R1Z.ProverCommitScalar48
open Aeneas Aeneas.Std Result AspisR1ProducerRelease47
open ProverCommitPrimitive47 ProverCommitSubfieldOps47
open AspisR1.ExtractedCurrentQM31Exact (decode)
open AspisV8R15.ExactTowerBase (M31Exact QM31Exact)

def embed (y : U32) : QM31Exact := ⟨⟨(y.val : M31Exact),0⟩,0⟩

theorem word_canonical (x y : U32) : (ProverCommitInverse48.wordMul x y).val < AspisCircleGroupOrder.P := by
  change (x.val*y.val)%AspisCircleGroupOrder.P < AspisCircleGroupOrder.P
  exact Nat.mod_lt _ (by decide)

theorem word_decode (x y : U32) :
    ((ProverCommitInverse48.wordMul x y).val : M31Exact)=(x.val : M31Exact)*(y.val : M31Exact) :=
  ProverCommitInverse48.word_mul x y

def product (x : Old.Q) (y : U32) : Old.Q :=
  ⟨⟨ProverCommitInverse48.wordMul x.c0.a y,ProverCommitInverse48.wordMul x.c0.b y⟩,
   ⟨ProverCommitInverse48.wordMul x.c1.a y,ProverCommitInverse48.wordMul x.c1.b y⟩⟩

theorem product_canonical (x : Old.Q) (y : U32) : Canonical (product x y) :=
  ⟨⟨word_canonical _ _,word_canonical _ _⟩,⟨word_canonical _ _,word_canonical _ _⟩⟩

theorem product_value (x : Old.Q) (y : U32) : decode (product x y)=decode x*embed y := by
  apply QuadraticAlgebra.ext
  · apply QuadraticAlgebra.ext <;> simp [product,decode,embed,word_decode]
  · apply QuadraticAlgebra.ext <;> simp [product,decode,embed,word_decode]

theorem source_exact (x : Old.Q) (y : U32) :
    scalar_ref (ProverCommitNativeQ48.source x) y=ok (ProverCommitNativeQ48.source (product x y)) ∧
      Canonical (product x y) ∧ decode (product x y)=decode x*embed y := by
  refine ⟨?_,product_canonical x y,product_value x y⟩
  simp only [scalar_ref,ProverCommitNativeQ48.source,ProverCommitRelease47.convQ,
    ProverCommitRelease47.convC,fromQ,fromC,ProverCommitInverse48.release_multiply,
    bind_tc_ok,product]

#print axioms word_canonical
#print axioms word_decode
#print axioms product_canonical
#print axioms product_value
#print axioms source_exact
end R1Z.ProverCommitScalar48
