import R1Z.PV_Inv_NativeQ
import R1Z.ProverCommitScalar48
import R1Z.PV_Inv_Compression
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_Inv_NativeCompress
open Aeneas Aeneas.Std Result AspisR1ProducerRelease47
open ProverCommitPrimitive47 ProverCommitSubfieldOps47
open ProverCommitNativeQ48 (source)
open AspisR1.ExtractedCurrentQM31Exact (decode)

def loop (lambda : field.QM31) : field.QM31 → field.QM31 → List U32 → Result field.QM31
 | acc,_,[] => ok acc
 | acc,power,x::xs => do
   let term ← scalar_ref power x
   let next ← field.QM31.add acc term
   let power' ← field.QM31.mul power lambda
   loop lambda next power' xs

theorem exact_value (lambda acc power : Old.Q) (xs : List U32)
    (hl : Canonical lambda) (ha : Canonical acc) (hp : Canonical power) :
    ∃ z : Old.Q, loop (source lambda) (source acc) (source power) xs=ok (source z) ∧
      Canonical z ∧ decode z=PV_Inv_Compression.loop (decode lambda) (decode acc) (decode power)
        (xs.map ProverCommitScalar48.embed) := by
  induction xs generalizing acc power with
  | nil => exact ⟨acc,rfl,ha,rfl⟩
  | cons x xs ih =>
    obtain ⟨ht,hct,hvt⟩ := ProverCommitScalar48.source_exact power x
    obtain ⟨next,hn,hcn,hvn⟩ := ProverCommitNativeQ48.add acc (ProverCommitScalar48.product power x) ha hct
    obtain ⟨power',hp',hcp',hvp'⟩ := ProverCommitNativeQ48.mul power lambda hp hl
    obtain ⟨z,hz,hcz,hvz⟩ := ih next power' hcn hcp'
    refine ⟨z,?_,hcz,?_⟩
    · simp only [loop,ht,hn,hp',bind_tc_ok,hz]
    · simpa only [List.map_cons,PV_Inv_Compression.loop,hvn,hvt,hvp'] using hvz

#print axioms exact_value
end R1Z.PV_Inv_NativeCompress
