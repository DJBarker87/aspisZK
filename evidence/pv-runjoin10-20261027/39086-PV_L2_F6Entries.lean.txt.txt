import R1Z.PV_L2_F6EntriesStep
set_option autoImplicit false
namespace R1Z.PV_L2_F6Entries
open Aeneas Aeneas.Std Result R1CertCheck R1Z.PV_L2_Record
open R1Z.PV_L2_F6EntriesStep
def recorded 
  (ej : Slice Std.U32) (es : Slice Std.U32) (epo : Slice Std.U32)
  (eco : Slice Std.U32) (idx : Slice Std.U32) (coef : Slice Std.U32)
  (m : Std.Usize) (lane : Slice Std.U32) (wl : Slice Std.U32)
  (z1 : Slice Std.U32) (s1 : Std.Usize) (z2 : Slice Std.U32) (s2 : Std.Usize)
  (n2 : Std.Usize) (g : Slice Std.U32) (sg : Std.Usize) (ng : Std.Usize)
  (out : Slice Std.U32) (zero : Slice Std.U32) : Recorded Bool :=
  PV_L2_F6FlagLoop.loop 24 (PV_L2_F6EntriesStep.recorded ej es epo eco idx coef m lane wl z1 s1 z2 s2 n2 g sg ng out zero) m m.val true 0#usize
theorem erases 
  (ej : Slice Std.U32) (es : Slice Std.U32) (epo : Slice Std.U32)
  (eco : Slice Std.U32) (idx : Slice Std.U32) (coef : Slice Std.U32)
  (m : Std.Usize) (lane : Slice Std.U32) (wl : Slice Std.U32)
  (z1 : Slice Std.U32) (s1 : Std.Usize) (z2 : Slice Std.U32) (s2 : Std.Usize)
  (n2 : Std.Usize) (g : Slice Std.U32) (sg : Std.Usize) (ng : Std.Usize)
  (out : Slice Std.U32) (zero : Slice Std.U32) :
    (recorded ej es epo eco idx coef m lane wl z1 s1 z2 s2 n2 g sg ng out zero).value = ents_ok ej es epo eco idx coef m lane wl z1 s1 z2 s2 n2 g sg ng out zero := by
  unfold recorded
  apply PV_L2_F6FlagLoop.erases 24 (PV_L2_F6EntriesStep.recorded ej es epo eco idx coef m lane wl z1 s1 z2 s2 n2 g sg ng out zero) m (ents_ok_loop ej es epo eco idx coef m lane wl z1 s1 z2 s2 n2 g sg ng out zero)
  · intro flag index
    rw [recorded_erases]
    exact unroll ej es epo eco idx coef m lane wl z1 s1 z2 s2 n2 g sg ng out zero flag index
  · intro flag index after hs
    rw [recorded_erases] at hs
    exact increment ej es epo eco idx coef m lane wl z1 s1 z2 s2 n2 g sg ng out zero flag index after hs
  · omega
#print axioms erases
end R1Z.PV_L2_F6Entries
