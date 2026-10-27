import JGw_InstalledSlots
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGw_WriterCall
open Aeneas Aeneas.Std Result AspisR1CurrentCaller
open JGr_Geometry

theorem source (p : verifier.Prepared) (out : verifier.Accumulator)
    (flushed : Slice aspis_core.field.QM31) :
    installed.op16 digest p {out with weights:=⟨flushed.val,flushed.property⟩}
      JFx_NativeBytes.proof JFx_NativeBytes.publicInput ()=
    WAdm_SourceWriter.writer (Tx1Q_Install.digest digest) (Tx1Q_Carriers.prepared p)
      (Tx1Q_Carriers.accumulator {out with weights:=⟨flushed.val,flushed.property⟩})
      JFx_NativeBytes.proof JFx_NativeBytes.publicInput () := rfl
#print axioms source

/-- The retained byte identity must constrain this writer's returned vector. -/
theorem returned_bytes (p : verifier.Prepared) (out : verifier.Accumulator)
    (flushed : Slice aspis_core.field.QM31) (saved : alloc.vec.Vec U8)
    (call : installed.op16 digest p {out with weights:=⟨flushed.val,flushed.property⟩}
      JFx_NativeBytes.proof JFx_NativeBytes.publicInput ()=ok saved) :
    WAdm_SourceWriter.writer (Tx1Q_Install.digest digest) (Tx1Q_Carriers.prepared p)
      (Tx1Q_Carriers.accumulator {out with weights:=⟨flushed.val,flushed.property⟩})
      JFx_NativeBytes.proof JFx_NativeBytes.publicInput ()=ok saved := by
  rw [←source]
  exact call
#print axioms returned_bytes
end AspisR1.JGw_WriterCall
end
