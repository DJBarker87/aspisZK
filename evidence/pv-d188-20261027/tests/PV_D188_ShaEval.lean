import R1Z.PV_CBL_FallbackBlock
open Aeneas Aeneas.Std Result
#eval (do let s ← PV_CBL_FallbackBlock.sha_fallback_reference.extracted_block
            (Array.repeat 8#usize 1#u32) (Array.repeat 16#usize 2#u32)
          ok (s.val.map (fun x => x.val)) : Result (List Nat))
