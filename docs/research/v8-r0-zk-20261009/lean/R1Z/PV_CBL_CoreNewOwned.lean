-- Exact extracted owned constructor types/body; namespaces only, no generated options.
import Aeneas
open Aeneas Aeneas.Std Result
namespace PV_CBL_CoreNewOwned


/-- [pv_cblib_source::ShaCoreOwned]
    Source: 'lib.rs', lines 389:0-389:62
    Visibility: public -/
structure ShaCoreOwned where
  state : Array Std.U32 8#usize
  block_len : Std.U64

/-- [pv_cblib_source::InvalidOutputSizeOwned]
    Source: 'lib.rs', lines 391:0-391:34
    Visibility: public -/
@[reducible]
def InvalidOutputSizeOwned := Unit


/-- [pv_cblib_source::sha_core_new_owned]:
    Source: 'lib.rs', lines 392:0-400:1
    Visibility: public -/
def sha_core_new_owned
  (output_size : Std.Usize) :
  Result (core.result.Result ShaCoreOwned InvalidOutputSizeOwned)
  := do
  match output_size.val with
  | 28 =>
    ok (core.result.Result.Ok
      {
        state :=
          (Array.make 8#usize [
            3238371032#u32, 914150663#u32, 812702999#u32, 4144912697#u32,
            4290775857#u32, 1750603025#u32, 1694076839#u32, 3204075428#u32
            ]),
        block_len := 0#u64
      })
  | 32 =>
    ok (core.result.Result.Ok
      {
        state :=
          (Array.make 8#usize [
            1779033703#u32, 3144134277#u32, 1013904242#u32, 2773480762#u32,
            1359893119#u32, 2600822924#u32, 528734635#u32, 1541459225#u32
            ]),
        block_len := 0#u64
      })
  | _ => ok (core.result.Result.Err ())

#print axioms ShaCoreOwned
#print axioms InvalidOutputSizeOwned
#print axioms sha_core_new_owned
end PV_CBL_CoreNewOwned
