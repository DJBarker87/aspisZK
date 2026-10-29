import R1Z.PV_RDCD4_EncoderEntries
import R1Z.PV_RDCD4_Split194
import R1Z.PV_RDCD4_Option194
import R1Z.PV_RDCD4_Wrappers194
import R1Z.PV_RDCD4_ArrayMemory194
import R1Z.PV_RDCD4_MemorySplit194
import R1Z.PV_RDCD4_ChunkMemory194
open Aeneas Aeneas.Std Result ProverRwFull
namespace R1Z.PV_RDCD4_V201
set_option autoImplicit false

/-- Source-value interpretation using the concrete 1.94.1 forward iterator
states. Source bindings, feature selection and compiler boundaries are audited
separately; this definition alone does not install an actual native producer. -/
def value {E : Type} (inst : aspis_core.r0.scalar.CodeField E)
    (q : Array E 1024#usize) (p : aspis_core.r0.domain.Point E) : Result E := do
  let basis ← PV_DL_EncoderBasis.value inst p.x
  let p0 ← inst.ZERO
  let p1 ← inst.ZERO
  let (p0,p1) ← PV_RDCD4_EncoderLoop.loop (PV_RDCD4_EncoderEntries.fieldStep inst) 513
    (PV_RDCD4_Zip194.new (PV_RDCD4_Chunks194.new q.val)
      (PV_RDCD4_ArrayIter194.new basis.val)) (p0,p1)
  let product ← inst.mul p.y p1
  inst.add p0 product

/-- Intended op79 consumption theorem; its complete original Result and
original CodeField parameter boundary are retained. -/
theorem source_reference {E : Type} (inst : aspis_core.r0.scalar.CodeField E)
    (q : Array E 1024#usize) (p : aspis_core.r0.domain.Point E) :
    value inst q p=PV_CB_OwnedEncoder.owned.encoder inst q p := by
  trans PV_DL_EncoderNative.value inst q p
  · unfold value PV_DL_EncoderNative.value
    apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
    intro basis _
    apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
    intro zero0 _
    apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
    intro zero1 _
    rw [PV_RDCD4_EncoderEntries.iteration]
  · exact PV_DL_EncoderNative.source_reference inst q p

#print axioms source_reference
end R1Z.PV_RDCD4_V201
