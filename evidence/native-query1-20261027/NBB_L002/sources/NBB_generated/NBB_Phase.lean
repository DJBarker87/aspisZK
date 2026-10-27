import S7OwnedP6ScalarProof
open Aeneas Aeneas.Std Result
set_option autoImplicit false
namespace NBB_Phase
open AspisR1BatchedFoldSourceStep

def Bound (terms raw : Nat) : Prop := raw < 2^34+(terms%4)*(2^31-2)^2

/-- The actual four-query flushing cadence preserves its exact envelope. -/
theorem next (terms raw a b : Nat) (ha : a<2^31-1) (hb : b<2^31-1)
 (hr : Bound terms raw) : Bound (terms+1) (sourcePush terms raw (a*b)) := by
 have product := product_bound ha hb
 change a*b≤(2^31-2)^2 at product
 have phase : terms%4<4 := Nat.mod_lt _ (by decide)
 have safe : raw+a*b<2^64 := by
  have h := Nat.mul_le_mul_right ((2^31-2)^2) (show terms%4≤3 by omega)
  unfold Bound at hr
  omega
 unfold Bound sourcePush
 split
 · have folded := fold_lt_two34 safe
   omega
 · have hn : (terms+1)%4=terms%4+1 := by omega
   rw [hn]
   unfold Bound at hr
   omega

/-- The scalar fragment is total on the SAME caller phase domain. -/
theorem scalar (raw : U64) (a b : U32) (terms : Nat)
 (ha : a.val<2^31-1) (hb : b.val<2^31-1) (hr : Bound terms raw.val) :
 ∃ out : U64,
 S7OwnedP6Scalar.residue_scalar_owned raw a b (decide (terms%4=3))=ok out ∧
 out.val=sourcePush terms raw.val (a.val*b.val) ∧ Bound (terms+1) out.val := by
 obtain ⟨out,run,value⟩ := S7OwnedP6ScalarProof.scalar_eq_source_push raw a b terms ha hb hr
 exact ⟨out,run,value,by rw [value];exact next terms raw.val a.val b.val ha hb hr⟩

/-- A native-compatible value is unique, including its full U64 carrier. -/
theorem unique (raw : U64) (a b : U32) (t : Nat) (x y : U64)
 (hx : x.val=sourcePush t raw.val (a.val*b.val))
 (hy : y.val=sourcePush t raw.val (a.val*b.val)) : x=y := by
 apply UScalar.eq_of_val_eq
 exact hx.trans hy.symm

#print axioms next
#print axioms scalar
#print axioms unique
end NBB_Phase
