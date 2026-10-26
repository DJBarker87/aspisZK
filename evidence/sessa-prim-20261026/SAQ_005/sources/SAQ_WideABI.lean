import SAQ_Query
import CurrentWideLinearExact
set_option autoImplicit false
noncomputable section
namespace AspisR1.SAQ_WideABI
open Aeneas Aeneas.Std Result
abbrev K := AspisR1Stage2.aspis_core.field.QM31
abbrev E := AspisR1Stage2.aspis_core.field.wide_exact.WideExact
abbrev Q := AspisR1CurrentWide.field.QM31
abbrev W := AspisR1CurrentWide.field.wide_exact.WideExact

def toQ (x : K) : Q := ⟨⟨x.c0.a,x.c0.b⟩,⟨x.c1.a,x.c1.b⟩⟩
def fromQ (x : Q) : K := ⟨⟨x.c0.a,x.c0.b⟩,⟨x.c1.a,x.c1.b⟩⟩
def toW (x : E) : W := ⟨toQ x.c0,toQ x.c1⟩
def fromW (x : W) : E := ⟨fromQ x.c0,fromQ x.c1⟩

theorem q_roundtrip (x : K) : fromQ (toQ x)=x := rfl
theorem w_roundtrip (x : E) : fromW (toW x)=x := rfl

theorem q_canonical (x : K) : Port3_FlushInstall.Canonical x ↔
    AspisR1CurrentWide.Proof.CanonicalQM (toQ x) := Iff.rfl

theorem w_canonical (x : E) : Port4C_QueryArithmetic.CanonE x ↔
    AspisR1CurrentWide.Proof.CanonicalWide (toW x) := Iff.rfl

theorem q_decode (x : K) : CheckpointBytes5Output.ofK x =
    AspisR1CurrentWide.Proof.decodeQM (toQ x) := by
  rfl

theorem w_decode (x : E) : CheckpointBytes5Output.ofE x =
    AspisR1CurrentWide.Proof.decodeWide (toW x) := by
  rw [CheckpointBytes5Output.ofE]
  change _ = ⟨AspisR1CurrentWide.Proof.decodeQM (toQ x.c0),
    AspisR1CurrentWide.Proof.decodeQM (toQ x.c1)⟩
  rw [q_decode,q_decode]

#print axioms q_roundtrip
#print axioms w_roundtrip
#print axioms q_canonical
#print axioms w_canonical
#print axioms q_decode
#print axioms w_decode
#check AspisR1CurrentWide.field.wide_exact.WideExact.mul_qm31
#check AspisR1CurrentWide.Proof.qm_mul_success
end AspisR1.SAQ_WideABI
end
