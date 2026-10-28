import R1Z.PV_RDCD_ZeroDrop
import R1Z.PV_RDCD_ZeroCursor
import R1Z.PV_RDCD_ZeroCompatibility
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RDCD_Audit
open Aeneas Aeneas.Std ProverRwFull
variable [ExternalTypes]

/-- Complete emitted byte-array Result plus the revised source world. The
native source association is separately scoped to emitted lengths32/64. -/
theorem v221 {F A : Type} (ops : ExternalFuns) (N : Usize)
    (a : Array U8 N) (address : Nat) (w : PV_RDCD_ZeroWorld.World F)
    (caller : Array U8 N → PV_RDCD_ZeroWorld.World F → Result A) :
    (do let a' ← (@Array.Insts.ZeroizeZeroize _ (PV_RDCD_ZeroSelected.selected ops) U8 N
          (@zeroize.Zeroize.Blanket _ (PV_RDCD_ZeroSelected.selected ops) U8
            U8.Insts.ZeroizeDefaultIsZeroes)).zeroize a
        caller a' (PV_RDCD_ZeroWorld.native address N.val w)) =
      caller (Array.repeat N 0#u8) (PV_RDCD_ZeroWorld.indexed address 0 N.val w) :=
  PV_RDCD_ZeroConsumed.emitted_execution ops N a address w caller

theorem v222 (ops : ExternalFuns) (x : U8) :
    (@zeroize.Zeroize.Blanket _ (PV_RDCD_ZeroSelected.selected ops) U8
      U8.Insts.ZeroizeDefaultIsZeroes).zeroize x=.ok 0#u8 := by
  rw [PV_RDCD_ZeroConsumed.emitted_scalar]
  exact PV_RDCD_ZeroSelected.byte_step x

theorem consumed_drop {F : Type} (ops : ExternalFuns) (N : Usize)
    (a : Array U8 N) (address : Nat) (w : PV_RDCD_ZeroWorld.World F) :
    PV_RDCD_ZeroDrop.dropArray ops N a address w=
      .ok ((),PV_RDCD_ZeroWorld.indexed address 0 N.val w) :=
  PV_RDCD_ZeroDrop.complete ops N a address w

#print axioms v221
#print axioms v222
#print axioms consumed_drop
#print axioms PV_RDCD_ZeroWorld.source_reference
#print axioms PV_RDCD_ZeroWorld.counts
#print axioms PV_RDCD_ZeroWorld.frame
#print axioms PV_RDCD_ZeroWorld.outside
#print axioms PV_RDCD_ZeroWorld.overwritten
#print axioms PV_RDCD_ZeroCursor.source
#print axioms PV_RDCD_ZeroCursor.drop_semicolon
#print axioms PV_RDCD_ZeroTrace.history
#print axioms PV_RDCD_ZeroTrace.writes_recorded
#print axioms PV_RDCD_ZeroTrace.nonvacuous
#print axioms PV_RDCD_ZeroCompatibility.trace_information
end R1Z.PV_RDCD_Audit
