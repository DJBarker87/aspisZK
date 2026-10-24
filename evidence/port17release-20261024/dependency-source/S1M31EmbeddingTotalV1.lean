import S1M31EmbeddingSourceV1
import CurrentPreparedInstalledMeaning
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisS1M31Embedding.Total
open AspisS1M31Embedding

def reduce (x : U32) : U32 := ⟨BitVec.umod x.bv (2147483647#u32).bv⟩

theorem reduce_val (x : U32) : (reduce x).val=x.val%2147483647 := by
  change (x.bv % (2147483647#32)).toNat=x.bv.toNat%2147483647
  rw [BitVec.toNat_umod]
  rfl

theorem reduce_idempotent (x : U32) : reduce (reduce x)=reduce x := by
  apply UScalar.eq_of_val_eq
  simp only [reduce_val,Nat.mod_mod]

theorem reduce_zero : reduce 0#u32=0#u32 := by rfl

theorem rem_total (x : U32) : x%aspis_core.field.P=ok (reduce x) := by
  unfold aspis_core.field.P
  rfl

def value (x : U32) : aspis_core.field.wide_exact.WideExact :=
  ⟨⟨⟨reduce x,0#u32⟩,⟨0#u32,0#u32⟩⟩,⟨⟨0#u32,0#u32⟩,⟨0#u32,0#u32⟩⟩⟩

/-- TOTAL actual emitted CodeField path, including both normalization passes,
for every raw M31 word. No canonical input or successful-child premise. -/
theorem source_total (x : U32) : source_from_m31 x=ok (value x) := by
  simp only [source_from_m31,
    aspis_core.field.wide_exact.WideExact.Insts.Aspis_coreR0ScalarCodeField.from_m31,
    aspis_core.field.QM31.Insts.Aspis_coreR0ScalarCodeField.from_m31,
    aspis_core.field.CM31.Insts.Aspis_coreR0ScalarCodeField.from_m31,
    aspis_core.field.M31.Insts.Aspis_coreR0ScalarCodeField.from_m31,
    rem_total,bind_tc_ok,aspis_core.field.CM31.from_m31,
    aspis_core.field.QM31.from_cm31,aspis_core.field.M31.ZERO,
    aspis_core.field.CM31.ZERO,aspis_core.field.wide_exact.WideExact.from_qm31,
    aspis_core.field.wide_exact.canonical_qm31,
    aspis_core.field.wide_exact.canonical_qm31.closure.Insts.CoreOpsFunctionFnTupleM31M31.call,
    reduce_idempotent,reduce_zero,aspis_core.field.QM31.ZERO,value]

abbrev PrepWide := AspisR1PublicPreparation.aspis_core.field.WideExact

def toPrep (x : aspis_core.field.wide_exact.WideExact) : PrepWide :=
  ⟨⟨⟨x.c0.c0.a,x.c0.c0.b⟩,⟨x.c0.c1.a,x.c0.c1.b⟩⟩,
   ⟨⟨x.c1.c0.a,x.c1.c0.b⟩,⟨x.c1.c1.a,x.c1.c1.b⟩⟩⟩

/-- Concrete caller child, retaining all eight emitted field coordinates. -/
def embed (x : AspisR1PublicPreparation.aspis_core.field.M31) : Result PrepWide := do
  let out ← source_from_m31 x
  ok (toPrep out)

theorem embed_total (x : AspisR1PublicPreparation.aspis_core.field.M31) :
    embed x=ok (toPrep (value x)) := by
  rw [embed,source_total,bind_tc_ok]

theorem embed_canonical (x : AspisR1PublicPreparation.aspis_core.field.M31) :
    AspisR1CurrentPreparedClaim.Concrete.Canonical
      (AspisR1ClaimPreparedBridge.toClaimE (toPrep (value x))) := by
  have h : (reduce x).val<2147483647 := by rw [reduce_val];exact Nat.mod_lt _ (by decide)
  have z : (0#u32).val<2147483647 := by decide
  exact ⟨⟨⟨h,z⟩,⟨z,z⟩⟩,⟨⟨z,z⟩,⟨z,z⟩⟩⟩

#print axioms reduce_val
#print axioms reduce_idempotent
#print axioms source_total
#print axioms embed_total
#print axioms embed_canonical
end AspisS1M31Embedding.Total
