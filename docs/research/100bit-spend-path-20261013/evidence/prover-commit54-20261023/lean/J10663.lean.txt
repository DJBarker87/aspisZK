import R1Z.ProverCommitEncoderM31Ops54
import R1Z.ProverCommitNativeQ48
/-! Concrete native QM31 methods discharge all generic encoder operations. -/
set_option autoImplicit false
namespace R1Z.ProverCommitEncoderQOps54
open Aeneas Aeneas.Std Result AspisR1ProducerRelease47
open ProverCommitPrimitive47 ProverCommitSubfieldOps47 ProverCommitEncoderGenericEval54
open AspisR1.ExtractedCurrentQM31Exact (decode QM31Exact)

def raw (q : field.QM31) : Old.Q := ⟨⟨q.c0.a,q.c0.b⟩,⟨q.c1.a,q.c1.b⟩⟩
def valid (q : field.QM31) : Prop := Canonical (raw q)
def value (q : field.QM31) : QM31Exact := decode (raw q)
def base (m : U32) : Old.Q := ⟨⟨m,0#u32⟩,⟨0#u32,0#u32⟩⟩
def nv (m : U32) : QM31Exact := decode (base m)

theorem source_raw (q : field.QM31) : ProverCommitNativeQ48.source (raw q)=q := rfl

theorem raw_source (q : Old.Q) : raw (ProverCommitNativeQ48.source q)=q := rfl

def ops (unused : scalar.CodeField field.QM31) : scalar.CodeField field.QM31 :=
  { unused with
    from_m31 := field.QM31.Insts.Aspis_r1_encoder53ScalarCodeField.from_m31
    add := field.QM31.Insts.Aspis_r1_encoder53ScalarCodeField.add
    sub := field.QM31.Insts.Aspis_r1_encoder53ScalarCodeField.sub
    mul := field.QM31.Insts.Aspis_r1_encoder53ScalarCodeField.mul }

theorem from_result (m : U32) (hm : m.val<2147483647) :
    field.QM31.Insts.Aspis_r1_encoder53ScalarCodeField.from_m31 m=ok (ProverCommitNativeQ48.source (base m)) := by
  simp only [field.QM31.Insts.Aspis_r1_encoder53ScalarCodeField.from_m31,
    field.CM31.Insts.Aspis_r1_encoder53ScalarCodeField.from_m31,
    ProverCommitEncoderM31Ops54.from_result m hm,field.CM31.from_m31,field.QM31.from_cm31,
    field.M31.ZERO,field.CM31.ZERO,bind_tc_ok,
    ProverCommitNativeQ48.source,ProverCommitRelease47.convQ,ProverCommitRelease47.convC,fromQ,fromC,base]

theorem arithmetic (unused : scalar.CodeField field.QM31) :
    Arithmetic (ops unused) valid value nv := by
  constructor
  · intro x y hx hy
    obtain ⟨z,hz,hcz,hdz⟩ := ProverCommitNativeQ48.add (raw x) (raw y) hx hy
    refine ⟨ProverCommitNativeQ48.source z,?_,?_,?_⟩
    · simpa only [ops,field.QM31.Insts.Aspis_r1_encoder53ScalarCodeField.add,source_raw] using hz
    · simpa only [valid,raw_source] using hcz
    · simpa only [value,raw_source] using hdz
  · intro x y hx hy
    obtain ⟨z,hz,hcz,hdz⟩ := ProverCommitNativeQ48.mul (raw x) (raw y) hx hy
    refine ⟨ProverCommitNativeQ48.source z,?_,?_,?_⟩
    · simpa only [ops,field.QM31.Insts.Aspis_r1_encoder53ScalarCodeField.mul,source_raw] using hz
    · simpa only [valid,raw_source] using hcz
    · simpa only [value,raw_source] using hdz
  · intro m hm
    refine ⟨ProverCommitNativeQ48.source (base m),from_result m hm,?_,?_⟩
    · change Canonical (raw (ProverCommitNativeQ48.source (base m)))
      rw [raw_source]
      change (m.val<2147483647 ∧ (0#u32).val<2147483647) ∧ ((0#u32).val<2147483647 ∧ (0#u32).val<2147483647)
      exact ⟨⟨hm,by decide⟩,⟨by decide,by decide⟩⟩
    · rw [value,raw_source,nv]

theorem sub_success (unused : scalar.CodeField field.QM31) (x y : field.QM31)
    (hx : valid x) (hy : valid y) :
    ∃ z, (ops unused).sub x y=ok z ∧ valid z ∧ value z=value x-value y := by
  obtain ⟨z,hz,hcz,hdz⟩ := ProverCommitNativeQ48.sub (raw x) (raw y) hx hy
  refine ⟨ProverCommitNativeQ48.source z,?_,?_,?_⟩
  · simpa only [ops,field.QM31.Insts.Aspis_r1_encoder53ScalarCodeField.sub,source_raw] using hz
  · simpa only [valid,raw_source] using hcz
  · simpa only [value,raw_source] using hdz

#print axioms source_raw
#print axioms raw_source
#print axioms from_result
#print axioms arithmetic
#print axioms sub_success
end R1Z.ProverCommitEncoderQOps54
