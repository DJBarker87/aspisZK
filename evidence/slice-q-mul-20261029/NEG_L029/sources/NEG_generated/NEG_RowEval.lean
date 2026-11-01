import NEG_RowIsolated.Funs
open Aeneas Aeneas.Std Result
#print Aeneas.Std.loop
#eval (do
  let r ← NEG_RowIsolated.update_residue_row
    (Array.make 4#usize [2147483648#u64,2147483649#u64,2147483650#u64,2147483651#u64])
    ⟨⟨0#u32,0#u32⟩,⟨0#u32,0#u32⟩⟩ 0#u32 true
  ok (r.val.map (fun x => x.val)) : Result (List Nat))
