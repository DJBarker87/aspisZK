import NHM_DotPacket
set_option autoImplicit false
namespace NHM_DotInitial
open Aeneas Aeneas.Std Result AspisR1

def zero : NHM_DotPacket.Dot :=
 ⟨⟨Array.make 4#usize [0#u64,0#u64,0#u64,0#u64]⟩,
  ⟨Array.make 4#usize [0#u64,0#u64,0#u64,0#u64]⟩,0#usize⟩

theorem source : FIo_Native.fast_pairing.EbyKDot.new=ok zero := by rfl

theorem count : zero.count.val=0 := by rfl

#print axioms source
#print axioms count
end NHM_DotInitial
