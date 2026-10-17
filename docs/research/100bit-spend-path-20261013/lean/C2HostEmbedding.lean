import AspisC2HostEmbedding.Funs

/-! Actual extracted host Wide embedding/projection primitive. No Backend,
constructor, encoder, literal-word or custody conclusion follows from this file.
The four raw QM31 limbs are reduced modulo P; raw representatives are not
silently treated as unchanged. -/
set_option autoImplicit false
namespace AspisR1.C2HostEmbedding
open Aeneas Aeneas.Std Result
open AspisC2HostEmbedding

def reduce (x : U32) : U32 := ⟨BitVec.umod x.bv (2147483647#u32).bv⟩

def canonical (q : field.QM31) : field.QM31 :=
  ⟨⟨reduce q.c0.a, reduce q.c0.b⟩, ⟨reduce q.c1.a, reduce q.c1.b⟩⟩

def embed (q : field.QM31) : field.wide_exact.WideExact :=
  ⟨canonical q, field.QM31.ZERO⟩

theorem reduce_val (x : U32) : (reduce x).val = x.val % 2147483647 := by
  change (x.bv % (2147483647#32)).toNat = x.bv.toNat % 2147483647
  rw [BitVec.toNat_umod]
  rfl

theorem reduce_lt (x : U32) : (reduce x).val < 2147483647 := by
  rw [reduce_val]
  exact Nat.mod_lt _ (by decide)

theorem canonical_bounded (q : field.QM31) :
    (canonical q).c0.a.val < 2147483647 ∧
    (canonical q).c0.b.val < 2147483647 ∧
    (canonical q).c1.a.val < 2147483647 ∧
    (canonical q).c1.b.val < 2147483647 :=
  ⟨reduce_lt _, reduce_lt _, reduce_lt _, reduce_lt _⟩

private theorem rem_success (x : U32) : x % field.P = ok (reduce x) := by
  unfold field.P
  rfl

/-- The actual canonicalizer succeeds at every raw four-limb input. -/
theorem canonical_success (q : field.QM31) :
    field.wide_exact.canonical_qm31 q = ok (canonical q) := by
  simp only [field.wide_exact.canonical_qm31,
    field.wide_exact.canonical_qm31.closure.Insts.CoreOpsFunctionFnTupleM31M31.call,
    rem_success, bind_tc_ok, canonical]

/-- Exact result, including the actual zero upper coordinate. -/
theorem embed_success (q : field.QM31) :
    field.wide_exact.WideExact.from_qm31 q = ok (embed q) := by
  simp only [field.wide_exact.WideExact.from_qm31, canonical_success, bind_tc_ok, embed]

theorem project_success (q : field.QM31) :
    embed_project_entry q = ok (canonical q) := by
  simp only [embed_project_entry, embed_success, bind_tc_ok,
    field.wide_exact.WideExact.impl.c0, embed]

/-- Exact primitive binding usable by a conditional owner model. -/
theorem project_embed (q : field.QM31) : (embed q).c0 = canonical q := rfl

theorem upper_zero (q : field.QM31) : (embed q).c1 = field.QM31.ZERO := rfl

#print axioms reduce_val
#print axioms reduce_lt
#print axioms canonical_bounded
#print axioms field.M31
#print axioms field.CM31
#print axioms field.QM31
#print axioms field.wide_exact.WideExact
#print axioms field.wide_exact.canonical_qm31.closure
#print axioms field.P
#print axioms field.QM31.ZERO
#print axioms field.wide_exact.canonical_qm31.closure.Insts.CoreOpsFunctionFnTupleM31M31.call
#print axioms field.wide_exact.canonical_qm31
#print axioms field.wide_exact.WideExact.from_qm31
#print axioms field.wide_exact.WideExact.impl.c0
#print axioms embed_project_entry
#print axioms canonical_success
#print axioms embed_success
#print axioms project_success
#print axioms project_embed
#print axioms upper_zero
end AspisR1.C2HostEmbedding
