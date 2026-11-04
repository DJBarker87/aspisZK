import NFQ_STAGE2_IMPORT
set_option autoImplicit false
namespace NFT_WideNew
open Aeneas Aeneas.Std Result AspisR1Post25Sampler

def reduce (x : U32) : U32 := ⟨BitVec.umod x.bv (2147483647#u32).bv⟩
def canonical (q : field.QM31) : field.QM31 :=
  ⟨⟨reduce q.c0.a,reduce q.c0.b⟩,⟨reduce q.c1.a,reduce q.c1.b⟩⟩

theorem reduce_val (x : U32) : (reduce x).val=x.val%2147483647 := by
  change (x.bv % (2147483647#32)).toNat=x.bv.toNat%2147483647
  rw [BitVec.toNat_umod]
  rfl

theorem reduce_lt (x : U32) : (reduce x).val<2147483647 := by
  rw [reduce_val]
  exact Nat.mod_lt _ (by decide)

theorem word_source (x : U32) :
    field.canonical_qm31.closure.Insts.CoreOpsFunctionFnTupleM31M31.call () x=ok (reduce x) := by
  simp only [field.canonical_qm31.closure.Insts.CoreOpsFunctionFnTupleM31M31.call,field.P]
  rfl

theorem canonical_source (q : field.QM31) : field.canonical_qm31 q=ok (canonical q) := by
  simp only [field.canonical_qm31,word_source,bind_tc_ok,canonical]

theorem source (a b : field.QM31) :
    field.WideExact.new a b=ok (⟨canonical a,canonical b⟩ : field.WideExact) := by
  simp only [field.WideExact.new,canonical_source,bind_tc_ok]

#print axioms reduce_val
#print axioms reduce_lt
#print axioms word_source
#print axioms canonical_source
#print axioms source
end NFT_WideNew
