import ProverRwSampler.Funs
open Aeneas Aeneas.Std Result ProverRwSampler
-- Tests only; all four inputs are at most 32 bytes.
#eval ([0#u32, 2147483647#u32, 2147483648#u32].map fun n =>
  (do let b ← lift (Array.to_slice (Array.repeat 32#usize 0#u8))
      let a ← lift (Array.to_slice (core.num.U32.to_le_bytes n))
      let b ← Slice.update b 0#usize (a.val[0]!)
      let b ← Slice.update b 1#usize (a.val[1]!)
      let b ← Slice.update b 2#usize (a.val[2]!)
      let b ← Slice.update b 3#usize (a.val[3]!)
      let block := Array.from_slice (Array.repeat 32#usize 0#u8) b
      let v ← sampler.qm31_sample block
      ok [v.c0.a.val,v.c0.b.val,v.c1.a.val,v.c1.b.val] : Result (List Nat)))
#eval (do let v ← sampler.qm31_sample (Array.repeat 32#usize 255#u8)
          ok [v.c0.a.val,v.c0.b.val,v.c1.a.val,v.c1.b.val] : Result (List Nat))
