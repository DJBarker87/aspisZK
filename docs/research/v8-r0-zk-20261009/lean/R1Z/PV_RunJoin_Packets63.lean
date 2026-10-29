import R1Z.PV_RunJoin_NativeFrames63
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_Packets63
open Aeneas Aeneas.Std Result ProverRwFull PV_RunJoin_NativeResidual63

variable {S F : Type} (base : ExternalTypes) (heap : Heap) (box : Box)
    (ops : @ExternalFuns (types base))
    (runtime : @PV_RunJoin_AllocatorWorld63.Runtime (types base) S F)
    (world : PV_FXM_ReserveWorld.World S F)

theorem mask_source :
    @ExternalFuns.op132 (types base) (opsNative base heap box ops runtime world)=
      ok (.Ok PV_B3P_Install132.value) := by
  rw [PV_RunJoin_NativeFrames63.op132]
  rfl

theorem mask_reference :
    @ExternalFuns.op132 (types base) (opsNative base heap box ops runtime world)=
      (do let (out,_) ← PV_B3P_132.reference132.cells
          let v : alloc.vec.Vec aspis_statement.trace_v4.TraceCell :=
            ⟨out.val.map PV_B3P_Install132.convert,by
              have h := out.property; simp only [List.length_map]; scalar_tac⟩
          ok (.Ok v)) := by
  rw [PV_RunJoin_NativeFrames63.op132]
  exact PV_B3P_Install132.reference (types base) (PV_RunJoin_NativeResidual62.residual base ops)

theorem mask_value :
    PV_B3P_Install132.value.val.map (fun x => (x.row.val,x.column.val)) =
      PV_B3P_MaskModel132.cells := PV_B3P_Install132.value_law

theorem mask_count : PV_B3P_Install132.value.val.length=3803 :=
  PV_B3P_Install132.count_law

theorem mask_nonvacuity :
    ∃ v, @ExternalFuns.op132 (types base) (opsNative base heap box ops runtime world)=ok (.Ok v) :=
  ⟨PV_B3P_Install132.value,mask_source base heap box ops runtime world⟩

theorem reserve {T : Type} (Allocator : Type) (v : alloc.vec.Vec T) (n : Usize) :
    letI : ExternalTypes := types base
    @ExternalFuns.op32 (types base) (opsNative base heap box ops runtime world) T Allocator v n =
      ok (@PV_FXM_ReserveSelected.returned (types base) runtime.encode
        (@PV_RunJoin_AllocatorWorld63.execute (types base) T S F runtime world v n).returned,v) := by
  letI : ExternalTypes := types base
  rw [PV_RunJoin_NativeFrames63.op32]
  exact @PV_RunJoin_AllocatorWorld63.complete (types base) T S F runtime _ world Allocator v n

#print axioms mask_source
#print axioms mask_reference
#print axioms mask_value
#print axioms mask_count
#print axioms mask_nonvacuity
#print axioms reserve
end R1Z.PV_RunJoin_Packets63
