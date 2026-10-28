import R1Z.PV_RJDec_MemoryReserve
import R1Z.PV_RJDec_MemoryDrop
import R1Z.PV_RJDec_ReachedZero
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RJDec_MemoryInstalled
open Aeneas Aeneas.Std ProverRwFull PV_W_Threading
variable [ExternalTypes] {W S F D DF ZF AF C : Type}
def selected (ops : ExternalFuns)
    (m : PV_RunJoin_RuntimeMemory38.Memory W S F D DF ZF) (w : W) : ExternalFuns :=
  PV_RJDec_ZeroizingSelected.selected (PV_RunJoin_RuntimeMemorySource38.selected ops m w)
def algebra (base : PV_W_TypedEffects.Algebra W (Option C) Aeneas.Std.Error)
    (m : PV_RunJoin_RuntimeMemory38.Memory W S F D DF ZF)
    (z : PV_RJDec_AsmMemory.Memory W AF) :=
  PV_RJDec_AsmMemory.install (PV_RunJoin_RuntimeMemory38.algebra base m) z

theorem reserve (ops : ExternalFuns)
    (base : PV_W_TypedEffects.Algebra W (Option C) Aeneas.Std.Error)
    (m : PV_RunJoin_RuntimeMemory38.Memory W S F D DF ZF)
    (z : PV_RJDec_AsmMemory.Memory W AF) {T : Type} (Allocator : Type)
    (v : alloc.vec.Vec T) (n : Usize) (w : W) :
    (algebra base m z).reserve Allocator v n w =
      (PV_RunJoin_RuntimeMemory38.algebra base m).reserve Allocator v n w := rfl

theorem drop (base : PV_W_TypedEffects.Algebra W (Option C) Aeneas.Std.Error)
    (m : PV_RunJoin_RuntimeMemory38.Memory W S F D DF ZF)
    (z : PV_RJDec_AsmMemory.Memory W AF) (v : alloc.vec.Vec U32) (w : W) :
    (algebra base m z).dropWords v w =
      (PV_RunJoin_RuntimeMemory38.algebra base m).dropWords v w := rfl

theorem base_unchanged (base : PV_W_TypedEffects.Algebra W (Option C) Aeneas.Std.Error)
    (m : PV_RunJoin_RuntimeMemory38.Memory W S F D DF ZF)
    (z : PV_RJDec_AsmMemory.Memory W AF) : (algebra base m z).base=base := rfl

theorem array_complete (ops : ExternalFuns)
    (base : PV_W_TypedEffects.Algebra W (Option C) Aeneas.Std.Error)
    (m : PV_RunJoin_RuntimeMemory38.Memory W S F D DF ZF)
    (z : PV_RJDec_AsmMemory.Memory W AF) (N : Usize) (v : Array U8 N) (w : W) :
    (algebra base m z).zeroArray N v w =
      ⟨PV_W_SourceSyntax.resultOutcome
        ((selected ops m w).op130 (@Array.Insts.ZeroizeZeroize _ (selected ops m w) U8 N
          (@zeroize.Zeroize.Blanket _ (selected ops m w) U8 U8.Insts.ZeroizeDefaultIsZeroes)) v),
        z.commit w (PV_RDCD_ZeroWorld.indexed (z.arrayAddress w v) 0 N.val (z.view w)),[(w,none)]⟩ := by
  rw [show (selected ops m w).op130 _ v = .ok (Array.repeat N 0#u8) from
    PV_RJDec_ZeroizingSelected.wrapper (PV_RunJoin_RuntimeMemorySource38.selected ops m w) N v]
  exact PV_RJDec_AsmMemory.array_complete z N v w

#print axioms reserve
#print axioms drop
#print axioms base_unchanged
#print axioms array_complete
end R1Z.PV_RJDec_MemoryInstalled
