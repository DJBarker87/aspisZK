import LIBC_Bytes
import LIBC_ExpandValuesModel
import LIB_VCarriers
set_option autoImplicit false
noncomputable section
namespace LIBC_ExpandValues
open Aeneas Aeneas.Std Result RSL
abbrev CodecErr := LIB_VCarriers.CodecErr
def Domain (a : Bytes × Bytes) : Prop := a.1.length ≤ 1856 ∧ a.2.length ≤ 3712
def Good (a : Bytes × Bytes) : Prop := a.1.length % 16 = 0 ∧ a.2.length = 2*a.1.length
instance (a : Bytes × Bytes) : Decidable (Good a) := inferInstanceAs (Decidable (_ ∧ _))
def value (a : Bytes × Bytes) (_ : Env) : Except CodecErr Bytes :=
 if Good a then .ok (LIB_Carriers.bytes
   (LIBC_ExpandValuesModel.output (LIBC_Bytes.raw a.1) (LIBC_Bytes.raw a.2)))
 else .error .Length
def child : Child (Bytes × Bytes) (Except CodecErr Bytes) :=
 LIB_Carriers.ofFn Domain value (fun _ _ => [])
/-- A native Err is exactly Length on this complete leaf domain (native_result).
Its mutable byte frame is exported before the RSL Result carrier port. -/
def port (r : core.result.Result Unit NFU_Retarget.compact.CodecError × Slice U8) :
 Except CodecErr Bytes := match r.1 with
 | .Ok _ => .ok (LIB_Carriers.bytes r.2)
 | .Err _ => .error .Length
theorem native_result (a : Bytes × Bytes) (h : Domain a) :
 NFU_Retarget.compact.expand_values (LIBC_Bytes.raw a.1) (LIBC_Bytes.raw a.2) =
 ok (if Good a then (.Ok (),LIBC_ExpandValuesModel.output (LIBC_Bytes.raw a.1) (LIBC_Bytes.raw a.2))
     else (.Err .Length,LIBC_Bytes.raw a.2)) := by
 have b1 : a.1.length ≤ Usize.max := by have : 1856 ≤ Usize.max := by scalar_tac;omega
 have b2 : a.2.length ≤ Usize.max := by have : 3712 ≤ Usize.max := by scalar_tac;omega
 have l1 := LIBC_Bytes.raw_length a.1 b1
 have l2 := LIBC_Bytes.raw_length a.2 b2
 rw [LIBC_ExpandValuesModel.source _ _ (by rw [l1];exact h.1),l1,l2]
 rfl
theorem model_port (a : Bytes × Bytes) (env : Env) (h : Domain a) :
 (do let r ← NFU_Retarget.compact.expand_values (LIBC_Bytes.raw a.1) (LIBC_Bytes.raw a.2)
     ok (port r)) = ok (value a env) := by
 rw [native_result a h]
 by_cases good : Good a <;> simp only [good,if_true,if_false,bind_tc_ok,port,value]
theorem exact (a : Bytes × Bytes) (env : Env) (o : Obs (Except CodecErr Bytes)) :
 child.law a env o ↔ o = ⟨.ret (value a env),[]⟩ := Iff.rfl
theorem returns (a : Bytes × Bytes) (env : Env) :
 NND_Returned.Returns (child.law a) env (value a env) := LIB_Carriers.ofFn_returns _ _ _ a env
theorem native_arguments (src dst : Slice U8) :
 (LIBC_Bytes.raw (LIB_Carriers.bytes src),LIBC_Bytes.raw (LIB_Carriers.bytes dst)) =
 (src,dst) := by rw [LIBC_Bytes.from_native,LIBC_Bytes.from_native]
#print axioms native_result
#print axioms model_port
#print axioms exact
#print axioms returns
#print axioms native_arguments
end LIBC_ExpandValues
