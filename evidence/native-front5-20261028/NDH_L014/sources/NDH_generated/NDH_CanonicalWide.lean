import AspisR1Post25Sampler.Funs
set_option autoImplicit false
namespace NDH_CanonicalWide
open Aeneas Aeneas.Std Result AspisR1Post25Sampler

def reduced (x : U32) : U32 :=
  ⟨BitVec.umod x.bv (2147483647#u32).bv⟩

theorem rem_success (x : U32) : (x % field.P : Result U32) = .ok (reduced x) := by
  unfold field.P
  rfl

theorem reduced_val (x : U32) :
    (reduced x).val = x.val % 2147483647 := by
  change (x.bv % (2147483647#32)).toNat = x.bv.toNat % 2147483647
  rw [BitVec.toNat_umod]
  rfl

theorem reduced_eq_self (x : U32) (hx : x.val < 2147483647) :
    reduced x = x := by
  apply UScalar.eq_of_val_eq
  rw [reduced_val, Nat.mod_eq_of_lt hx]

theorem canonical_success (q : field.QM31)
    (h0 : q.c0.a.val < 2147483647) (h1 : q.c0.b.val < 2147483647)
    (h2 : q.c1.a.val < 2147483647) (h3 : q.c1.b.val < 2147483647) :
    field.canonical_qm31 q = .ok q := by
  have r0 : (q.c0.a % field.P : Result U32) = .ok q.c0.a := by
    rw [rem_success, reduced_eq_self _ h0]
  have r1 : (q.c0.b % field.P : Result U32) = .ok q.c0.b := by
    rw [rem_success, reduced_eq_self _ h1]
  have r2 : (q.c1.a % field.P : Result U32) = .ok q.c1.a := by
    rw [rem_success, reduced_eq_self _ h2]
  have r3 : (q.c1.b % field.P : Result U32) = .ok q.c1.b := by
    rw [rem_success, reduced_eq_self _ h3]
  simp only [field.canonical_qm31,
    field.canonical_qm31.closure.Insts.CoreOpsFunctionFnTupleM31M31.call,
    r0, r1, r2, r3, bind_tc_ok]


#print axioms rem_success
#print axioms reduced_val
#print axioms reduced_eq_self
#print axioms canonical_success
end NDH_CanonicalWide
