import R1Z.PV_DL_EncoderBasis
import R1Z.PV_DL_EncoderFold
open Aeneas Aeneas.Std Result ProverRwFull
namespace R1Z.PV_DL_EncoderControl
set_option autoImplicit false

theorem duplicate {E R : Type} (r : Result E) (f : E → E → Result R) :
    (do let a ← r;let b ← r;f a b)=(do let a ← r;f a a) := by
  cases r <;> rfl

/-- Native forward `chunks_exact(2).zip(basis)` control after the proved
index/basis transport. Field operations are the original CodeField inputs. -/
def value {E : Type} (inst : aspis_core.r0.scalar.CodeField E)
    (q : Array E 1024#usize) (p : aspis_core.r0.domain.Point E) : Result E := do
  let basis ← PV_DL_EncoderBasis.value inst p.x
  let z0 ← inst.ZERO
  let z1 ← inst.ZERO
  let (p0,p1) ← PV_DL_EncoderFold.finite inst q basis 512 0#usize z0 z1
  let yp1 ← inst.mul p.y p1
  inst.add p0 yp1

theorem source_reference {E : Type} (inst : aspis_core.r0.scalar.CodeField E)
    (q : Array E 1024#usize) (p : aspis_core.r0.domain.Point E) :
    PV_CB_OwnedEncoder.owned.encoder inst q p=value inst q p := by
  unfold PV_CB_OwnedEncoder.owned.encoder value
  rw [PV_DL_EncoderBasis.basis_source]
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro basis hb
  rw [duplicate inst.ZERO (fun a b => do
    let (p0,p1) ← PV_DL_EncoderFold.finite inst q basis 512 0#usize a b
    let yp1 ← inst.mul p.y p1
    inst.add p0 yp1)]
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro zero hz
  rw [PV_DL_EncoderFold.source inst q basis 512 0#usize zero zero (by decide)]

/-- The fixed native input domains contain inputs for every inhabited E. -/
theorem inputs_nonempty {E : Type} [Nonempty E] :
    Nonempty (Array E 1024#usize × aspis_core.r0.domain.Point E) := by
  obtain ⟨e⟩ := ‹Nonempty E›
  exact ⟨(Array.repeat 1024#usize e,⟨e,e⟩)⟩

#print axioms duplicate
#print axioms value
#print axioms source_reference
#print axioms inputs_nonempty
end R1Z.PV_DL_EncoderControl
