import LIBC_Bytes
import LIBC_ExpandSemanticModel
import LIB_VCarriers
set_option autoImplicit false
noncomputable section
namespace LIBC_ExpandSemantic
open Aeneas Aeneas.Std Result RSL
abbrev CodecErr := LIB_VCarriers.CodecErr
def Domain (a : Bytes × Bytes) : Prop := a.1.length=7015 ∧ a.2.length=13831
def value (a : Bytes × Bytes) (_ : Env) : Except CodecErr Bytes :=
 .ok (LIB_Carriers.bytes (LIBC_ExpandSemanticModel.output (LIBC_Bytes.raw a.1)))
def child : Child (Bytes × Bytes) (Except CodecErr Bytes) :=
 LIB_Carriers.ofFn Domain value (fun _ _ => [])
theorem native_result (a : Bytes × Bytes) (h : Domain a) :
 AspisS1NativeCompact.compact.expand_semantic AspisS1ValuesOwnedInstallation.nativeValues
  (LIBC_Bytes.raw a.1) (LIBC_Bytes.raw a.2) =
 ok (.Ok (),LIBC_ExpandSemanticModel.output (LIBC_Bytes.raw a.1)) := by
 have b1 : a.1.length ≤ Usize.max := by rw [h.1];scalar_tac
 have b2 : a.2.length ≤ Usize.max := by rw [h.2];scalar_tac
 exact LIBC_ExpandSemanticModel.source _ _
  ((LIBC_Bytes.raw_length _ b1).trans h.1) ((LIBC_Bytes.raw_length _ b2).trans h.2)
theorem model_port (a : Bytes × Bytes) (env : Env) (h : Domain a) :
 (do let r ← AspisS1NativeCompact.compact.expand_semantic AspisS1ValuesOwnedInstallation.nativeValues
       (LIBC_Bytes.raw a.1) (LIBC_Bytes.raw a.2)
     ok (match r.1 with
       | .Ok _ => Except.ok (LIB_Carriers.bytes r.2)
       | .Err _ => Except.error (.Length : CodecErr))) = ok (value a env) := by
 rw [native_result a h,bind_tc_ok]
 rfl
theorem returns (a : Bytes × Bytes) (env : Env) :
 NND_Returned.Returns (child.law a) env (value a env) := LIB_Carriers.ofFn_returns _ _ _ a env
theorem exact (a : Bytes × Bytes) (env : Env) (o : Obs (Except CodecErr Bytes)) :
 child.law a env o ↔ o = ⟨.ret (value a env),[]⟩ := Iff.rfl
/-- Symbolic length transport prevents reduction of a concrete 13,831-cell list. -/
theorem bytes_ofFn_length {n : Nat} (f : Fin n → U8)
 (h : (List.ofFn f).length ≤ Usize.max) :
 (LIB_Carriers.bytes (⟨List.ofFn f,h⟩ : Slice U8)).length = n := by
 change (List.map _ (List.ofFn f)).length = n
 rw [List.length_map,List.length_ofFn]
theorem output_length (src : Slice U8) :
 (LIB_Carriers.bytes (LIBC_ExpandSemanticModel.output src)).length = 13831 :=
 bytes_ofFn_length (LIBC_ExpandSemanticModel.byte src) _

#print axioms native_result
#print axioms model_port
#print axioms returns
#print axioms exact
#print axioms bytes_ofFn_length
#print axioms output_length
end LIBC_ExpandSemantic
