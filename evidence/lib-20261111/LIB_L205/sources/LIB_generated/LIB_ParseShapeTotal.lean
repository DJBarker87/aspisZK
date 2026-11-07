import LIBC_ParseShape
import Op3I_Header
set_option autoImplicit false
noncomputable section
namespace LIB_ParseShapeTotal
open Aeneas Aeneas.Std Result RSL
abbrev model := LIBC_ParseShape.model
abbrev port := LIBC_ParseShape.port
/-- The source guard precedes every slice access and every child operation. -/
theorem wrong_length_native (ops : Op3I_Source.ParseShapeOps) (proof : Slice U8)
 (h : proof.val.length ≠ 57607) :
 Op3I_Source.verifier.candidate.parse_shape ops proof =
 ok (.Err Op3I_Source.verifier.Error.Parse) := by
 have guard : (Slice.len proof != 57607#usize) = true := by
  simp only [bne_iff_ne]
  intro eq
  apply h
  have hv := congrArg UScalar.val eq
  simpa [Slice.len] using hv
 simp only [Op3I_Source.verifier.candidate.parse_shape,Op3I_Header.proof_bytes,bind_tc_ok,guard,ite_true]
/-- The byte carrier is total; nonrepresentable lists map to an empty native
slice, which also fails the length guard. Every actual native slice roundtrips. -/
theorem wrong_length (proof : Bytes) (env : Env) (h : proof.length ≠ 57607) :
 model proof env = ok (.Err Op3I_Source.verifier.Error.Parse) := by
 apply wrong_length_native
 by_cases bound : proof.length ≤ Usize.max
 · simpa only [LIBC_Bytes.raw_length proof bound] using h
 · simp only [LIBC_Bytes.raw,dif_neg bound,List.length_nil]
   exact Nat.zero_ne_add_one _
def child : Child Bytes (Except LIB_VCarriers.VErr Unit) :=
 ⟨fun _ => True,fun proof => LIB_Carriers.resultGraph port (model proof) (fun _ => [])⟩
abbrev value := LIBC_ParseShape.value
theorem domain (proof : Bytes) : child.dom proof := True.intro
theorem graph (proof : Bytes) (env : Env) (o : Obs (Except LIB_VCarriers.VErr Unit)) :
 child.law proof env o ↔ o = LIB_Carriers.resultObs port [] (model proof env) := Iff.rfl
/-- Preserve the entire CLOSED086 graph on its original installed domain. -/
theorem closed086 (proof : Bytes) (_h : LIBC_ParseShape.Domain proof) :
 child.law proof = LIBC_ParseShape.child.law proof := rfl
/-- Fresh frozen emission equality is unconditional on the original native slice. -/
theorem source (proof : Slice U8) (env : Env) :
 model (LIB_Carriers.bytes proof) env =
 NJS_Parse.map NJS_Parse.reply
  (NJS_Extract.verifier.candidate.parse_shape Op3I_Std.ops.sliceNe Op3I_Std.ops.sliceEq Op3I_Std.ops.iterAny proof) :=
 LIBC_ParseShape.source proof env
theorem rejected (proof : Bytes) (env : Env) (h : proof.length ≠ 57607)
 (o : Obs (Except LIB_VCarriers.VErr Unit)) :
 child.run proof env o ↔ o = ⟨.ret (.error .Parse),[]⟩ := by
 change (True ∧ o = LIB_Carriers.resultObs port [] (model proof env)) ↔ _
 rw [wrong_length proof env h]
 exact and_iff_right True.intro
theorem returns (proof : Bytes) (env : Env) :
 NND_Returned.Returns (child.law proof) env (value proof env) :=
 LIBC_ParseShape.returns proof env
theorem functional : Child.Functional child := by
 intro proof _
 exact LIBC_ResultGraph.functional port (model proof) (fun _ => [])
#print axioms wrong_length_native
#print axioms wrong_length
#print axioms domain
#print axioms graph
#print axioms closed086
#print axioms source
#print axioms rejected
#print axioms returns
#print axioms functional
end LIB_ParseShapeTotal
