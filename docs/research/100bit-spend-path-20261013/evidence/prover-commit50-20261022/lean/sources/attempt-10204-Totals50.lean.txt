import AspisR1ProducerRelease47.Channels49
/-! Extracted counter owner, with identical arithmetic callees rebound to the
previously proved release extraction. bind-counter.py checks every reused
callee declaration body byte-for-byte. No external template is installed. -/
open Aeneas Aeneas.Std Result ControlFlow Error
noncomputable section
namespace AspisR1ProducerRelease47
def totals50.channel
  (a : Array (Array (Array field.M31 3#usize) 3#usize) 3#usize)
  (b : Array (Array (Array field.M31 3#usize) 3#usize) 3#usize) (c : Std.Usize)
  (h : Std.Usize) :
  Result Std.U64
  := do
  let a1 ← Array.index_usize a 0#usize
  let a2 ← Array.index_usize a1 c
  let m ← Array.index_usize a2 h
  let a3 ← Array.index_usize a 1#usize
  let a4 ← Array.index_usize a3 c
  let m1 ← Array.index_usize a4 h
  let a5 ← Array.index_usize a 2#usize
  let a6 ← Array.index_usize a5 c
  let m2 ← Array.index_usize a6 h
  let a7 ← Array.index_usize b 0#usize
  let a8 ← Array.index_usize a7 c
  let m3 ← Array.index_usize a8 h
  let a9 ← Array.index_usize b 1#usize
  let a10 ← Array.index_usize a9 c
  let m4 ← Array.index_usize a10 h
  let a11 ← Array.index_usize b 2#usize
  let a12 ← Array.index_usize a11 c
  let m5 ← Array.index_usize a12 h
  channels.sum (Array.make 3#usize [ m, m1, m2 ])
    (Array.make 3#usize [ m3, m4, m5 ]) 0#usize 3#u8 0#u64

def totals50.all
  (a : Array (Array (Array field.M31 3#usize) 3#usize) 3#usize)
  (b : Array (Array (Array field.M31 3#usize) 3#usize) 3#usize) :
  Result (Array (Array Std.U64 3#usize) 3#usize)
  := do
  let i ← totals50.channel a b 0#usize 0#usize
  let i1 ← totals50.channel a b 0#usize 1#usize
  let i2 ← totals50.channel a b 0#usize 2#usize
  let i3 ← totals50.channel a b 1#usize 0#usize
  let i4 ← totals50.channel a b 1#usize 1#usize
  let i5 ← totals50.channel a b 1#usize 2#usize
  let i6 ← totals50.channel a b 2#usize 0#usize
  let i7 ← totals50.channel a b 2#usize 1#usize
  let i8 ← totals50.channel a b 2#usize 2#usize
  ok
    (Array.make 3#usize [
      Array.make 3#usize [ i, i1, i2 ], Array.make 3#usize [ i3, i4, i5 ],
      Array.make 3#usize [ i6, i7, i8 ]
      ])

end AspisR1ProducerRelease47
