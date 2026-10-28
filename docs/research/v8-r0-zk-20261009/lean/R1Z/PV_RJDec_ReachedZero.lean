import R1Z.PV_RJDec_ZeroizingSelected
import R1Z.PV_RJDec_AsmMemory
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RJDec_ReachedZero
open Aeneas Aeneas.Std ProverRwFull PV_W_Threading
variable [ExternalTypes] {W F C : Type}
/-- The exact source thunk retained in PV_W_R_ReserveBuild. -/
def op (v : zeroize.Zeroizing (Array U8 32#usize)) :
    PV_W_SourceSyntax.Op (zeroize.Zeroizing (Array U8 32#usize)) :=
  ⟨"zeroize.Zeroizing.Insts.ZeroizeZeroize.zeroize",fun ops =>
    @zeroize.Zeroizing.Insts.ZeroizeZeroize.zeroize _ ops _
      (@Array.Insts.ZeroizeZeroize _ ops U8 32#usize
        (@zeroize.Zeroize.Blanket _ ops U8 U8.Insts.ZeroizeDefaultIsZeroes)) v⟩

theorem source (ops : ExternalFuns) (v : Array U8 32#usize) :
    (op v).source (PV_RJDec_ZeroizingSelected.selected ops) =
      .ok (Array.repeat 32#usize 0#u8) :=
  PV_RJDec_ZeroizingSelected.wrapper ops 32#usize v

/-- Complete typed interpreter construction for that call, now using the
restored world law. Native view/commit and base-helper routing remain P. -/
theorem complete (ops : ExternalFuns) (m : PV_RJDec_AsmMemory.Memory W F)
    (v : Array U8 32#usize) (w : W) :
    PV_RJDec_AsmMemory.array (C := C) m 32#usize v w =
      ⟨PV_W_SourceSyntax.resultOutcome ((op v).source (PV_RJDec_ZeroizingSelected.selected ops)),
        m.commit w (PV_RDCD_ZeroWorld.indexed (m.arrayAddress w v) 0 32 (m.view w)),[(w,none)]⟩ := by
  rw [source]
  exact PV_RJDec_AsmMemory.array_complete m 32#usize v w
#print axioms source
#print axioms complete
end R1Z.PV_RJDec_ReachedZero
