import R1Z.PV_RDCD_ZeroConsumed
import R1Z.PV_W_ReachedThreading
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RJDec_AsmMemory
open Aeneas Aeneas.Std ProverRwFull PV_W_Threading
variable [ExternalTypes] {W F C : Type}
structure Memory (W F : Type) where
  view : W → PV_RDCD_ZeroWorld.World F
  commit : W → PV_RDCD_ZeroWorld.World F → W
  arrayAddress : {N : Usize} → W → Array U8 N → Nat
  byteAddress : W → U8 → Nat

def array (m : Memory W F) (N : Usize) (v : Array U8 N) :
    M W (Option C) Aeneas.Std.Error (Array U8 N) := fun w =>
  ⟨.ok (Array.repeat N 0#u8),
    m.commit w (PV_RDCD_ZeroWorld.native (m.arrayAddress w v) N.val (m.view w)),[(w,none)]⟩
def byte (m : Memory W F) (v : U8) : M W (Option C) Aeneas.Std.Error U8 := fun w =>
  ⟨.ok 0#u8,m.commit w (PV_RDCD_ZeroWorld.byte (m.byteAddress w v) (m.view w)),[(w,none)]⟩
/-- Replace only the two byte handlers; reserve, word drop and all base helpers
are preserved. Association of view/commit with native memory remains required. -/
def install (a : PV_W_ReachedThreading.Algebra W (Option C)) (m : Memory W F) :
    PV_W_ReachedThreading.Algebra W (Option C) :=
  {a with zeroArray := array m,zeroByte := byte m}

theorem array_complete (m : Memory W F) (N : Usize) (v : Array U8 N) (w : W) :
    array (C := C) m N v w =
      ⟨.ok (Array.repeat N 0#u8),
        m.commit w (PV_RDCD_ZeroWorld.indexed (m.arrayAddress w v) 0 N.val (m.view w)),[(w,none)]⟩ := by
  unfold array
  rw [show PV_RDCD_ZeroWorld.native (m.arrayAddress w v) N.val (m.view w) =
    PV_RDCD_ZeroWorld.indexed (m.arrayAddress w v) 0 N.val (m.view w) from
      PV_RDCD_ZeroWorld.caller_composition _ _ _ id]
#print axioms array_complete
end R1Z.PV_RJDec_AsmMemory
