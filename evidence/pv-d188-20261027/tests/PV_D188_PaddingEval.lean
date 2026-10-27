import R1Z.PV_CBL_ShaPadFixed
import R1Z.PV_CBL_ArrayKernel
open Aeneas Aeneas.Std Result
#eval (do let v ← PV_CBL_ShaPadFixed.sha_pad_zero (Array.repeat 64#usize 255#u8) 3#usize
          ok (v.val.map (fun x => x.val)) : Result (List Nat))
#eval (do let v ← PV_CBL_ShaPadFixed.sha_pad_suffix8 (Array.repeat 64#usize 255#u8) (Array.repeat 8#usize 7#u8)
          ok (v.val.map (fun x => x.val)) : Result (List Nat))
#eval (do let s ← lift (Array.to_slice (Array.make 4#usize [1#u32,2#u32,3#u32,4#u32]))
          let v ← PV_CBL_ArrayKernel.array_reference 4#usize core.marker.CopyU32 s 0#u32
          ok (v.map (fun a => a.val.map (fun x => x.val))) : Result (Option (List Nat)))
