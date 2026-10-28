import R1Z.ProverRwFullTypes
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow Error ProverRwFull
namespace R1Z.ProverRwDictionaryBytesSource

def aspis_core.field.P : Std.U32 := 2147483647#u32

def aspis_core.field.wide_exact.WideExact.BYTE_LEN : Std.Usize := 32#usize

def aspis_core.field.wide_exact.WideExact.from_limbs
  (limbs : Array Std.U32 8#usize) :
  Result (Option aspis_core.field.wide_exact.WideExact)
  := do
  let i ← Array.index_usize limbs 0#usize
  if i >= aspis_core.field.P
  then ok none
  else
    let i1 ← Array.index_usize limbs 1#usize
    if i1 >= aspis_core.field.P
    then ok none
    else
      let i2 ← Array.index_usize limbs 2#usize
      if i2 >= aspis_core.field.P
      then ok none
      else
        let i3 ← Array.index_usize limbs 3#usize
        if i3 >= aspis_core.field.P
        then ok none
        else
          let i4 ← Array.index_usize limbs 4#usize
          if i4 >= aspis_core.field.P
          then ok none
          else
            let i5 ← Array.index_usize limbs 5#usize
            if i5 >= aspis_core.field.P
            then ok none
            else
              let i6 ← Array.index_usize limbs 6#usize
              if i6 >= aspis_core.field.P
              then ok none
              else
                let i7 ← Array.index_usize limbs 7#usize
                if i7 >= aspis_core.field.P
                then ok none
                else
                  ok (some
                    {
                      c0 :=
                        { c0 := { a := i, b := i1 }, c1 := { a := i2, b := i3 }
                        },
                      c1 :=
                        {
                          c0 := { a := i4, b := i5 },
                          c1 := { a := i6, b := i7 }
                        }
                    })

def aspis_core.field.wide_exact.WideExact.to_limbs
  (self : aspis_core.field.wide_exact.WideExact) :
  Result (Array Std.U32 8#usize)
  := do
  let i := self.c0.c0.a
  let i1 := self.c0.c0.b
  let i2 := self.c0.c1.a
  let i3 := self.c0.c1.b
  let i4 := self.c1.c0.a
  let i5 := self.c1.c0.b
  let i6 := self.c1.c1.a
  let i7 := self.c1.c1.b
  ok (Array.make 8#usize [ i, i1, i2, i3, i4, i5, i6, i7 ])

def aspis_core.field.wide_exact.WideExact.from_le_bytes
  (bytes : Slice Std.U8) :
  Result (Option aspis_core.field.wide_exact.WideExact)
  := do
  let i := Slice.len bytes
  if i != aspis_core.field.wide_exact.WideExact.BYTE_LEN
  then ok none
  else
    let i1 ← Slice.index_usize bytes 0#usize
    let i2 ← Slice.index_usize bytes 1#usize
    let i3 ← Slice.index_usize bytes 2#usize
    let i4 ← Slice.index_usize bytes 3#usize
    let i5 ←
      lift (core.num.U32.from_le_bytes (Array.make 4#usize [ i1, i2, i3, i4 ]))
    let i6 ← Slice.index_usize bytes 4#usize
    let i7 ← Slice.index_usize bytes 5#usize
    let i8 ← Slice.index_usize bytes 6#usize
    let i9 ← Slice.index_usize bytes 7#usize
    let i10 ←
      lift (core.num.U32.from_le_bytes (Array.make 4#usize [ i6, i7, i8, i9 ]))
    let i11 ← Slice.index_usize bytes 8#usize
    let i12 ← Slice.index_usize bytes 9#usize
    let i13 ← Slice.index_usize bytes 10#usize
    let i14 ← Slice.index_usize bytes 11#usize
    let i15 ←
      lift (core.num.U32.from_le_bytes
        (Array.make 4#usize [ i11, i12, i13, i14 ]))
    let i16 ← Slice.index_usize bytes 12#usize
    let i17 ← Slice.index_usize bytes 13#usize
    let i18 ← Slice.index_usize bytes 14#usize
    let i19 ← Slice.index_usize bytes 15#usize
    let i20 ←
      lift (core.num.U32.from_le_bytes
        (Array.make 4#usize [ i16, i17, i18, i19 ]))
    let i21 ← Slice.index_usize bytes 16#usize
    let i22 ← Slice.index_usize bytes 17#usize
    let i23 ← Slice.index_usize bytes 18#usize
    let i24 ← Slice.index_usize bytes 19#usize
    let i25 ←
      lift (core.num.U32.from_le_bytes
        (Array.make 4#usize [ i21, i22, i23, i24 ]))
    let i26 ← Slice.index_usize bytes 20#usize
    let i27 ← Slice.index_usize bytes 21#usize
    let i28 ← Slice.index_usize bytes 22#usize
    let i29 ← Slice.index_usize bytes 23#usize
    let i30 ←
      lift (core.num.U32.from_le_bytes
        (Array.make 4#usize [ i26, i27, i28, i29 ]))
    let i31 ← Slice.index_usize bytes 24#usize
    let i32 ← Slice.index_usize bytes 25#usize
    let i33 ← Slice.index_usize bytes 26#usize
    let i34 ← Slice.index_usize bytes 27#usize
    let i35 ←
      lift (core.num.U32.from_le_bytes
        (Array.make 4#usize [ i31, i32, i33, i34 ]))
    let i36 ← Slice.index_usize bytes 28#usize
    let i37 ← Slice.index_usize bytes 29#usize
    let i38 ← Slice.index_usize bytes 30#usize
    let i39 ← Slice.index_usize bytes 31#usize
    let i40 ←
      lift (core.num.U32.from_le_bytes
        (Array.make 4#usize [ i36, i37, i38, i39 ]))
    aspis_core.field.wide_exact.WideExact.from_limbs
      (Array.make 8#usize [ i5, i10, i15, i20, i25, i30, i35, i40 ])

def aspis_core.field.M31.to_le_bytes
  (self : aspis_core.field.M31) : Result (Array Std.U8 4#usize) := do
  ok (core.num.U32.to_le_bytes self)

def aspis_core.field.CM31.write_le_bytes
  (self : aspis_core.field.CM31) (out : Slice Std.U8) :
  Result (Slice Std.U8)
  := do
  let (s, index_mut_back) ←
    core.slice.index.Slice.index_mut
      (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) out
      { start := 0#usize, «end» := 4#usize }
  let a ← aspis_core.field.M31.to_le_bytes self.a
  let s1 ← lift (Array.to_slice a)
  let s2 ← core.slice.Slice.copy_from_slice core.marker.CopyU8 s s1
  let out1 := index_mut_back s2
  let (s3, index_mut_back1) ←
    core.slice.index.Slice.index_mut
      (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) out1
      { start := 4#usize, «end» := 8#usize }
  let a1 ← aspis_core.field.M31.to_le_bytes self.b
  let s4 ← lift (Array.to_slice a1)
  let s5 ← core.slice.Slice.copy_from_slice core.marker.CopyU8 s3 s4
  ok (index_mut_back1 s5)

def aspis_core.field.QM31.write_le_bytes
  (self : aspis_core.field.QM31) (out : Slice Std.U8) :
  Result (Slice Std.U8)
  := do
  let (s, index_mut_back) ←
    core.slice.index.Slice.index_mut
      (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) out
      { start := 0#usize, «end» := 8#usize }
  let s1 ← aspis_core.field.CM31.write_le_bytes self.c0 s
  let out1 := index_mut_back s1
  let (s2, index_mut_back1) ←
    core.slice.index.Slice.index_mut
      (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) out1
      { start := 8#usize, «end» := 16#usize }
  let s3 ← aspis_core.field.CM31.write_le_bytes self.c1 s2
  ok (index_mut_back1 s3)

def aspis_core.field.CM31.new
  (a : aspis_core.field.M31) (b : aspis_core.field.M31) :
  Result aspis_core.field.CM31
  := do
  ok { a, b }
end R1Z.ProverRwDictionaryBytesSource
