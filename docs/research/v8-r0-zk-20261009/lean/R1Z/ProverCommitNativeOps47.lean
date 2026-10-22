import R1Z.ProverCommitSubfieldOps47
import R1Z.ProverCommitRelease47
/-! Constructor normalization and canonical embedded operations of the actual
release arithmetic extraction. These are primitive source facts, not a whole
simulator or evaluator certificate. -/
set_option autoImplicit false
namespace R1Z.ProverCommitNativeOps47
open Aeneas Aeneas.Std Result
open ProverCommitPrimitive47 ProverCommitSubfieldOps47 ProverCommitRelease47
open AspisR1.ExtractedCurrentQM31Exact

def normalizeWord (x : U32) : U32 := ⟨BitVec.umod x.bv (2147483647#u32).bv⟩
def normalize (x : Old.Q) : Old.Q :=
  ⟨⟨normalizeWord x.c0.a,normalizeWord x.c0.b⟩,
   ⟨normalizeWord x.c1.a,normalizeWord x.c1.b⟩⟩
def embedded (x : Old.Q) := convE (ProverCommitSubfieldOps47.embedded x)

theorem normalize_val (x : U32) : (normalizeWord x).val=x.val%2147483647 := by
  simp only [normalizeWord,UScalar.val]
  rfl

theorem normalize_canonical (x : Old.Q) : Canonical (normalize x) := by
  change ((normalizeWord x.c0.a).val<2147483647 ∧ (normalizeWord x.c0.b).val<2147483647) ∧
    ((normalizeWord x.c1.a).val<2147483647 ∧ (normalizeWord x.c1.b).val<2147483647)
  simp only [normalize_val]
  exact ⟨⟨Nat.mod_lt _ (by decide),Nat.mod_lt _ (by decide)⟩,
    ⟨Nat.mod_lt _ (by decide),Nat.mod_lt _ (by decide)⟩⟩

theorem normalize_cast (x : U32) :
    ((normalizeWord x).val : AspisV8R15.ExactTowerBase.M31Exact) = (x.val : AspisV8R15.ExactTowerBase.M31Exact) := by
  rw [normalize_val]
  change ((x.val%AspisCircleGroupOrder.P : Nat) : ZMod AspisCircleGroupOrder.P) = _
  exact ZMod.natCast_mod _ _

theorem normalize_decode (x : Old.Q) : decode (normalize x)=decode x := by
  apply QuadraticAlgebra.ext
  · apply QuadraticAlgebra.ext <;> exact normalize_cast _
  · apply QuadraticAlgebra.ext <;> exact normalize_cast _

theorem rem_source (x : U32) : x % (2147483647#u32) = ok (normalizeWord x) := by
  rfl

/-- Every raw source QM31 input is normalized by the actual release constructor.
No canonical-input or source-success premise is required. -/
theorem from_qm31 (x : Old.Q) :
    AspisR1ProducerRelease47.field.wide_exact.WideExact.from_qm31 (convQ (fromQ x)) =
      ok (embedded (normalize x)) ∧
    Canonical (normalize x) ∧ decode (normalize x)=decode x := by
  refine ⟨?_,normalize_canonical x,normalize_decode x⟩
  simp only [AspisR1ProducerRelease47.field.wide_exact.WideExact.from_qm31,
    AspisR1ProducerRelease47.field.wide_exact.canonical_qm31,
    AspisR1ProducerRelease47.field.wide_exact.canonical_qm31.closure.Insts.CoreOpsFunctionFnTupleM31M31.call,
    AspisR1ProducerRelease47.field.P,AspisR1ProducerRelease47.field.QM31.ZERO,convQ,convC,fromQ,fromC,rem_source,bind_tc_ok]
  rfl

/-- No checked-success premise remains in the release operation theorem. -/
theorem add_exact (x y : Old.Q) (hx : Canonical x) (hy : Canonical y) :
    ∃ z : Old.Q,
      AspisR1ProducerRelease47.field.wide_exact.WideExact.add (embedded x) (embedded y) = ok (embedded z) ∧
      Canonical z ∧ decode z=decode x+decode y := by
  obtain ⟨z,hz,hcanon,hdecode⟩ := ProverCommitSubfieldOps47.embedded_add x y hx hy
  exact ⟨z,ProverCommitRelease47.addE _ _ _ hz,hcanon,hdecode⟩

theorem mul_exact (x y : Old.Q) (hx : Canonical x) (hy : Canonical y) :
    ∃ z : Old.Q,
      AspisR1ProducerRelease47.field.wide_exact.WideExact.mul (embedded x) (embedded y) = ok (embedded z) ∧
      Canonical z ∧ decode z=decode x*decode y := by
  obtain ⟨z,hz,hcanon,hdecode⟩ := ProverCommitSubfieldOps47.embedded_mul x y hx hy
  exact ⟨z,ProverCommitRelease47.mulE _ _ _ hz,hcanon,hdecode⟩

#print axioms normalize_val
#print axioms normalize_canonical
#print axioms normalize_cast
#print axioms normalize_decode
#print axioms rem_source
#print axioms from_qm31
#print axioms add_exact
#print axioms mul_exact
end R1Z.ProverCommitNativeOps47
