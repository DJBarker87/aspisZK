import R1Z.ProverRwFullFuns
open Aeneas Aeneas.Std Result ProverRwFull
#eval (do
 let s ← lift (Array.to_slice (Array.make 3#usize [1#u16,3#u16,7#u16]))
 let v ← aspis_prover.state_only_hiding.active_rows s
 ok (v.val.take 8) : Result (List Bool))
#eval (do
 let v ← aspis_prover.state_only_entropy.source_active_flags_loop
   (Array.repeat 64#usize 1#u16) 1024#usize (Array.repeat 1024#usize false) 0#usize
 ok (v.val.take 32) : Result (List Bool))
#eval (do
 let v ← aspis_prover.state_only_hiding.mask_dependent_step
   (Array.repeat 16#usize (none : Option Usize)) 3#usize 7#usize false
 let r ← Array.index_usize v 3#usize
 ok (r.map (fun n => n.val)) : Result (Option Nat))
#eval (do
 let a ← Array.update (Array.repeat 16#usize 0#u32) 0#usize 1#u32
 let a ← Array.update a 1#usize 2#u32
 let a ← Array.update a 2#usize 3#u32
 let (a,n,m) ← host_tree.count_level a 3#usize
 ok (a.val.map (fun x => x.val),n.val,m.val) : Result (List Nat × Nat × Nat))
#eval (do
 let b ← Array.update (Array.repeat 32#usize 0#u8) 0#usize 2#u8
 let r ← host_transcript.scan_query_words (Array.repeat 8#usize b)
   (Array.repeat 8#usize (Array.repeat 32#usize 7#u8))
   (Array.repeat 22#usize 1#u32) 21#usize 0#usize
 match r with
 | .Ok (a,b) => ok (some (a.val.map (fun x => x.val),b.val.map (fun x => x.val)))
 | .Err _ => ok none : Result (Option (List Nat × List Nat)))
