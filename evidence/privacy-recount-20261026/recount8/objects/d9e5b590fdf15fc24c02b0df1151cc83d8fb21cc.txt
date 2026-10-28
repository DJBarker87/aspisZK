import R1Z.PV_RunJoin_RuntimeMemory38
import R1Z.PV_FXM_AuditInstall
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_RuntimeMemorySource38
open Aeneas Aeneas.Std ProverRwFull
variable [ExternalTypes]
variable {W S F D DF ZF C : Type}

def selected (ops : ExternalFuns) (m : PV_RunJoin_RuntimeMemory38.Memory W S F D DF ZF) (w : W) :=
  PV_FXM_AuditInstall.selected ops m.allocate m.wordMax m.byteMax m.shape
    (fun {T} (v : alloc.vec.Vec T) => m.metadata w v) m.encode (m.reserveView w)

theorem reserve (ops : ExternalFuns)
    (base : PV_W_TypedEffects.Algebra W (Option C) Aeneas.Std.Error)
    (m : PV_RunJoin_RuntimeMemory38.Memory W S F D DF ZF)
    {T : Type} (Allocator : Type) (v : alloc.vec.Vec T) (n : Usize) (w : W) :
    ((PV_RunJoin_RuntimeMemory38.algebra base m).reserve Allocator v n w).outcome =
      PV_W_SourceSyntax.resultOutcome ((selected ops m w).op32 Allocator v n) := by
  rw [show (selected ops m w).op32 Allocator v n = _ from
    PV_FXM_AuditInstall.reserve ops m.allocate m.wordMax m.byteMax m.shape
      (fun {T} (v : alloc.vec.Vec T) => m.metadata w v) m.encode (m.reserveView w) Allocator v n]
  rfl

theorem drop (ops : ExternalFuns)
    (base : PV_W_TypedEffects.Algebra W (Option C) Aeneas.Std.Error)
    (m : PV_RunJoin_RuntimeMemory38.Memory W S F D DF ZF) (v : alloc.vec.Vec U32) (w : W) :
    ((PV_RunJoin_RuntimeMemory38.algebra base m).dropWords v w).outcome =
      PV_W_SourceSyntax.resultOutcome ((selected ops m w).op4 v) := by
  rw [show (selected ops m w).op4 v = .ok () from
    PV_FXM_AuditInstall.drop ops m.allocate m.wordMax m.byteMax m.shape
      (fun {T} (v : alloc.vec.Vec T) => m.metadata w v) m.encode (m.reserveView w) v]
  rfl

theorem array (ops : ExternalFuns)
    (base : PV_W_TypedEffects.Algebra W (Option C) Aeneas.Std.Error)
    (m : PV_RunJoin_RuntimeMemory38.Memory W S F D DF ZF) (N : Usize) (v : Array U8 N) (w : W) :
    ((PV_RunJoin_RuntimeMemory38.algebra base m).zeroArray N v w).outcome =
      PV_W_SourceSyntax.resultOutcome ((selected ops m w).op122 PV_FXM_ZeroSelected.byteZero v) := by
  rw [show (selected ops m w).op122 PV_FXM_ZeroSelected.byteZero v = .ok (Array.repeat N 0#u8) from
    PV_FXM_AuditInstall.array ops m.allocate m.wordMax m.byteMax m.shape
      (fun {T} (v : alloc.vec.Vec T) => m.metadata w v) m.encode (m.reserveView w) v]
  rfl

theorem scalar (ops : ExternalFuns)
    (base : PV_W_TypedEffects.Algebra W (Option C) Aeneas.Std.Error)
    (m : PV_RunJoin_RuntimeMemory38.Memory W S F D DF ZF) (v : U8) (w : W) :
    ((PV_RunJoin_RuntimeMemory38.algebra base m).zeroByte v w).outcome =
      PV_W_SourceSyntax.resultOutcome ((selected ops m w).op123 PV_FXM_ZeroSelected.byteDefault v) := by
  rw [show (selected ops m w).op123 PV_FXM_ZeroSelected.byteDefault v = .ok 0#u8 from
    PV_FXM_AuditInstall.scalar ops m.allocate m.wordMax m.byteMax m.shape
      (fun {T} (v : alloc.vec.Vec T) => m.metadata w v) m.encode (m.reserveView w) v]
  rfl

/-- No terminal callback is installed by the memory effect interpreter. -/
theorem terminal_unchanged (ops : ExternalFuns)
    (m : PV_RunJoin_RuntimeMemory38.Memory W S F D DF ZF) (w : W) :
    (selected ops m w).op227=ops.op227 := rfl

#print axioms reserve
#print axioms drop
#print axioms array
#print axioms scalar
#print axioms terminal_unchanged
end R1Z.PV_RunJoin_RuntimeMemorySource38
