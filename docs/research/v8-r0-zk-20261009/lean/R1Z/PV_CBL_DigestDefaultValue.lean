import R1Z.PV_CBL_DigestSoft
import R1Z.PV_CBL_CoreNewOwned
open Aeneas Aeneas.Std Result
namespace R1Z.PV_CBL_DigestDefaultValue
set_option autoImplicit false
def state : Array U32 8#usize := Array.make 8#usize
  [1779033703#u32,3144134277#u32,1013904242#u32,2773480762#u32,
   1359893119#u32,2600822924#u32,528734635#u32,1541459225#u32]
theorem source : PV_CBL_DigestSoft.sha_default_soft_owned =
    ok (state,0#u64,Array.repeat 64#usize 0#u8,0#usize) := rfl
theorem constructor : PV_CBL_CoreNewOwned.sha_core_new_owned 32#usize =
    ok (.Ok {state := state,block_len := 0#u64}) := rfl
#print axioms constructor
#print axioms state
#print axioms source
end R1Z.PV_CBL_DigestDefaultValue
