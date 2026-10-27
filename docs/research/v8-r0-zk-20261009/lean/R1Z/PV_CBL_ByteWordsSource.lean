import R1Z.PV_CBL_ByteLane00
import R1Z.PV_CBL_ByteLane01
import R1Z.PV_CBL_ByteLane02
import R1Z.PV_CBL_ByteLane03
import R1Z.PV_CBL_ByteLane04
import R1Z.PV_CBL_ByteLane05
import R1Z.PV_CBL_ByteLane06
import R1Z.PV_CBL_ByteLane07
import R1Z.PV_CBL_ByteLane08
import R1Z.PV_CBL_ByteLane09
import R1Z.PV_CBL_ByteLane10
import R1Z.PV_CBL_ByteLane11
import R1Z.PV_CBL_ByteLane12
import R1Z.PV_CBL_ByteLane13
import R1Z.PV_CBL_ByteLane14
import R1Z.PV_CBL_ByteLane15
open Aeneas Aeneas.Std Result
namespace R1Z.PV_CBL_ByteWordsSource
set_option autoImplicit false
def value (b : Array U8 64#usize) : Array U32 16#usize :=
  Array.make 16#usize [PV_CBL_ByteLane00.value b,PV_CBL_ByteLane01.value b,PV_CBL_ByteLane02.value b,PV_CBL_ByteLane03.value b,PV_CBL_ByteLane04.value b,PV_CBL_ByteLane05.value b,PV_CBL_ByteLane06.value b,PV_CBL_ByteLane07.value b,PV_CBL_ByteLane08.value b,PV_CBL_ByteLane09.value b,PV_CBL_ByteLane10.value b,PV_CBL_ByteLane11.value b,PV_CBL_ByteLane12.value b,PV_CBL_ByteLane13.value b,PV_CBL_ByteLane14.value b,PV_CBL_ByteLane15.value b]
theorem source (b : Array U8 64#usize) : PV_CBL_ShaBytes.sha_load64 b = ok (value b) := by
  unfold PV_CBL_ShaBytes.sha_load64
  simp only [PV_CBL_ByteLane00.source,PV_CBL_ByteLane01.source,PV_CBL_ByteLane02.source,PV_CBL_ByteLane03.source,PV_CBL_ByteLane04.source,PV_CBL_ByteLane05.source,PV_CBL_ByteLane06.source,PV_CBL_ByteLane07.source,PV_CBL_ByteLane08.source,PV_CBL_ByteLane09.source,PV_CBL_ByteLane10.source,PV_CBL_ByteLane11.source,PV_CBL_ByteLane12.source,PV_CBL_ByteLane13.source,PV_CBL_ByteLane14.source,PV_CBL_ByteLane15.source,bind_tc_ok]
  rfl
#print axioms value
#print axioms source
end R1Z.PV_CBL_ByteWordsSource
