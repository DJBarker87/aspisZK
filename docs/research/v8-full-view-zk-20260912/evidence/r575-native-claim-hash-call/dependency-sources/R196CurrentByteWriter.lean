import AspisR156FullFreeze.FunsCore
import AspisV8R19.R144BeforeOodBytesBridge

/-! Apply the already proved generic byte serializer to the actual selected
field writer. The namespace/type bridge preserves arbitrary-input results and
errors, and does not reprove the generic serialization loop. -/
set_option autoImplicit false
namespace AspisV8R19.R196CurrentByteWriter
open Aeneas Aeneas.Std Result Aeneas.Std.WP
open AspisR156FullFreeze.aspis_core

def toCM (q : field.CM31) : AspisR137Transcript.field.CM31 := ⟨q.a,q.b⟩
def toBefore (q : field.QM31) : AspisR136BeforeOod.aspis_core.field.QM31 :=
  ⟨⟨q.c0.a,q.c0.b⟩,⟨q.c1.a,q.c1.b⟩⟩

theorem cm_writer_bridge (q : field.CM31) (out : Slice U8) :
    field.CM31.write_le_bytes q out =
      AspisR137Transcript.field.CM31.write_le_bytes (toCM q) out := by
  simp only [field.CM31.write_le_bytes,
    AspisR137Transcript.field.CM31.write_le_bytes, toCM,
    field.M31.to_le_bytes, AspisR137Transcript.field.M31.to_le_bytes]

theorem qm_writer_bridge (q : field.QM31) (out : Slice U8) :
    field.QM31.write_le_bytes q out =
      AspisR136BeforeOod.aspis_core.field.QM31.write_le_bytes (toBefore q) out := by
  simp only [field.QM31.write_le_bytes,
    AspisR136BeforeOod.aspis_core.field.QM31.write_le_bytes,
    AspisR137Transcript.field.QM31.write_le_bytes,
    AspisR136BeforeOod.toR137QM31, AspisR136BeforeOod.toR137CM31,
    toBefore, cm_writer_bridge, toCM]

theorem current_writer_exact (q : field.QM31) (out : Slice U8)
    (hout : out.length = 16) :
    field.QM31.write_le_bytes q out
      ⦃ r => r.val = R144BeforeOodBytesBridge.qm31Bytes (toBefore q) ⦄ := by
  rw [qm_writer_bridge]
  exact R144BeforeOodBytesBridge.qm31_write_exact (toBefore q) out hout

#print axioms cm_writer_bridge
#print axioms qm_writer_bridge
#print axioms current_writer_exact
end AspisV8R19.R196CurrentByteWriter
