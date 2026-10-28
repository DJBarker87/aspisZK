import R1Z.PV_FXM_AuditAxioms
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_FXM_Closure
open Aeneas Aeneas.Std ProverRwFull PV_FXM_ReserveWorld
variable [ExternalTypes]

/-- Focused closure replay of the four exact source-law callback scopes. This
packages already proved laws; it does not assert a deployed endpoint result. -/
theorem callbacks {T S F : Type} (ops : ExternalFuns)
    (step : Request → S → Option Nat × S) (wordMax byteMax : Nat)
    (shape : Type → Shape)
    (metadata : {U : Type} → (v : alloc.vec.Vec U) → PV_FXM_ReserveSelected.Metadata v)
    (h : alloc.collections.TryReserveError=PDict_ReserveError.alloc.collections.TryReserveError)
    (w : World S F) (level : alloc.vec.Vec U32) (N : Usize) (a : Array U8 N)
    (byte : U8) (Allocator : Type) (v : alloc.vec.Vec T) (n : Usize) :
    let encode := PV_FXM_ReserveSelected.encodeError h
    let o := PV_FXM_AuditInstall.selected ops step wordMax byteMax shape metadata encode w
    o.op4 level=.ok () ∧
    (@Array.Insts.ZeroizeZeroize _ o U8 N
      (@zeroize.Zeroize.Blanket _ o U8 U8.Insts.ZeroizeDefaultIsZeroes)).zeroize a=
        .ok (Array.repeat N 0#u8) ∧
    (@zeroize.Zeroize.Blanket _ o U8 U8.Insts.ZeroizeDefaultIsZeroes).zeroize byte=
      .ok 0#u8 ∧
    o.op32 Allocator v n=.ok (PV_FXM_ReserveSelected.returned encode
      (native step wordMax byteMax (shape T)
        (PV_FXM_ReserveSelected.buffer v (metadata v)) n.val w).returned,v) ∧
    {o with op4 := ops.op4,op32 := ops.op32,op122 := ops.op122,op123 := ops.op123}=ops := by
  dsimp only
  refine ⟨PV_FXM_AuditInstall.drop ops step wordMax byteMax shape metadata
      (PV_FXM_ReserveSelected.encodeError h) w level, ?_, ?_,
    PV_FXM_AuditInstall.reserve ops step wordMax byteMax shape metadata
      (PV_FXM_ReserveSelected.encodeError h) w Allocator v n,
    PV_FXM_AuditInstall.other_fields ops step wordMax byteMax shape metadata
      (PV_FXM_ReserveSelected.encodeError h) w⟩
  · exact PV_FXM_AuditInstall.array ops step wordMax byteMax shape metadata
      (PV_FXM_ReserveSelected.encodeError h) w a
  · exact PV_FXM_AuditInstall.scalar ops step wordMax byteMax shape metadata
      (PV_FXM_ReserveSelected.encodeError h) w byte

#print axioms callbacks
end R1Z.PV_FXM_Closure
