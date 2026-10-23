import AspisR1ProducerRelease47.EncoderNativeGeometry55
import R1Z.ProverCommitEncoderNativePower55
import R1Z.ProverCommitEncoderPoint54
import R1Z.ProverCommitEncoderNodes54
/-! The square-based source power gives exactly the retained canonical source
point and complete node array, not only equal field residues. -/
set_option autoImplicit false
namespace R1Z.ProverCommitNativeGeometry55
open Aeneas Aeneas.Std Result AspisR1ProducerRelease47
open ProverCommitPrimitive47 ProverCommitNativeC49
open AspisV8R15.ExactTowerBase

theorem canonical_injective (x y : Old.C) (hx : Canonical x) (hy : Canonical y)
    (h : value x=value y) : x=y := by
  let qx : Old.Q := ⟨x,⟨0#u32,0#u32⟩⟩
  let qy : Old.Q := ⟨y,⟨0#u32,0#u32⟩⟩
  have hqx : ProverCommitSubfieldOps47.Canonical qx := ⟨hx,by change (0#u32).val<2147483647 ∧ (0#u32).val<2147483647;constructor <;> decide⟩
  have hqy : ProverCommitSubfieldOps47.Canonical qy := ⟨hy,by change (0#u32).val<2147483647 ∧ (0#u32).val<2147483647;constructor <;> decide⟩
  have he : AspisR1.ExtractedCurrentQM31Exact.decode qx=AspisR1.ExtractedCurrentQM31Exact.decode qy :=
    congrArg (fun z : CM31Exact => (⟨z,0⟩ : QM31Exact)) h
  have eq := (AspisR1.ExtractedCurrentQM31Equality.decode_eq_iff qx qy hqx hqy).mp he
  exact congrArg (fun z : Old.Q => z.c0) eq

theorem power_same (exp : U64) (base acc : Old.C) (hb : Canonical base) (ha : Canonical acc) :
    nodes55.pow (source base) exp (source acc)=nodes54.pow (source base) exp (source acc) := by
  obtain ⟨x,hx,hcx,hdx⟩ := ProverCommitEncoderNativePower55.exact_result exp.val exp rfl base acc hb ha
  obtain ⟨y,hy,hcy,hdy⟩ := ProverCommitEncoderPower54.exact_result exp.val exp rfl base acc hb ha
  have he : x=y := canonical_injective x y hcx hcy (hdx.trans hdy.symm)
  rw [hx,hy,he]

attribute [local irreducible] source

theorem point_same (j : Usize) : nodes55.point j=nodes54.point j := by
  obtain ⟨r,hr,hrv⟩ := ProverCommitEncoderReverse54.exact_result 18 (by decide) 18#u8 rfl j
  rw [nodes55.point,nodes54.point,hr]
  simp only [field.CM31.new,lift,bind_tc_ok]
  have h := power_same (U64.wrapping_add 1024#u64 (U64.wrapping_mul 4096#u64 (UScalar.cast .U64 r)))
    ProverCommitEncoderPoint54.generator ProverCommitEncoderPoint54.one
    ProverCommitEncoderPoint54.generator_canonical ProverCommitEncoderPoint54.one_canonical
  simpa only [source,ProverCommitRelease47.convC,fromC,ProverCommitEncoderPoint54.generator,
    ProverCommitEncoderPoint54.one,field.CM31.ONE] using h

theorem node_same (j : Usize) (d : U8) : nodes55.node j d=nodes54.node j d := by
  rw [nodes55.node,nodes54.node]
  simp only [point_same]

#print axioms canonical_injective
#print axioms power_same
#print axioms point_same
#print axioms node_same
end R1Z.ProverCommitNativeGeometry55
