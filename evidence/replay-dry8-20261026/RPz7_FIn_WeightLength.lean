import RPz7_Cons_NativeBuild
import Port3_NativeQueryRaw
import Port3_NativePendingInstall
import Port3_FlushInstall
import RPz7_Tx2N_Fields
set_option autoImplicit false
namespace AspisR1.FIn_WeightLength
open Aeneas Aeneas.Std Result AspisR1Stage2

theorem twelve {C Hash : Type} (reserved : Bool)
    (query : Port3_NativeQueryBody.Ops) (geo : Port3_NativeGeometryBody.Ops C)
    (D : VTop_Stages.aspis_core.digest.Digest32 Hash) (hash : Hash)
    (pub proof checkpoint : Slice U8) (t : Cons_Native.Witness)
    (aux : Cons_NativeBuild.Aux reserved query geo D hash pub proof checkpoint t)
    (saved : t.saved2.weights.val.length=64) :
    (t.back2 t.flushed2).val.length=64 ∧ t.returned2.next.val=22 := by
  obtain ⟨hr,next,geometry,pending,queryCall,back,flush⟩ := aux
  have allocated := Port3_NativePendingInstall.accepted_fields reserved t.saved2.weights.deref
    t.pending2 saved pending
  have native := (Port3_QueryInstall.success_iff _ _).mp queryCall
  let row := Port4C_RowStd.install (Port5Q1_QueryPorts.install (Port3_QueryStage.release query))
  change Port3_NativeQueryBody.verifier.candidate.query_loop
    (Port3_NativeRowFrame.install row) proof t.p2 t.saved2 t.g2 none t.geometry2 t.pending2 22#usize =
      ok (.Ok (t.returned2,t.after2)) at native
  have frame := Port3_NativeQueryRaw.loop_raw row proof t.p2 t.saved2 t.returned2 t.g2
    none t.geometry2 t.pending2 t.after2 22#usize saved allocated.2.2.2 (by rw [next]; decide) native
  have size : t.returned2.weights.val.length=64 := by rw [frame.1]; exact saved
  have enough : t.returned2.weights.deref.val.length≤t.after2.raw.val.length := by
    change t.returned2.weights.val.length≤t.after2.raw.val.length
    rw [size,frame.2.1]
  have flushed := Port3_FlushInstall.accepted_contents t.after2 t.returned2.weights.deref t.flushed2 enough flush
  have backEq : t.back2=fun s => (⟨s.val,s.property⟩ : alloc.vec.Vec aspis_core.field.QM31) :=
    (congrArg Prod.snd back).symm
  rw [backEq]
  exact ⟨flushed.2.trans size,frame.2.2⟩

#print axioms twelve
end AspisR1.FIn_WeightLength
