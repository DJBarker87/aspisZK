import R1Z.ProverRwFullFuns
set_option autoImplicit false
namespace PDict_CodecSource
open Aeneas Aeneas.Std Result ProverRwFull
/-- [aspis_core::field::wide_exact::{aspis_core::field::wide_exact::WideExact}::BYTE_LEN]
    Source: '/home/dombarker/project-offloads/codex-cx-prover-dict-20261026/src/crates/aspis-core/src/field/wide_exact.rs', lines 35:4-35:29
    Name pattern: [aspis_core::field::wide_exact::{aspis_core::field::wide_exact::WideExact}::BYTE_LEN]
    Visibility: public -/
@[global_simps, irreducible, rust_const
  "aspis_core::field::wide_exact::{aspis_core::field::wide_exact::WideExact}::BYTE_LEN"]
def aspis_core.field.wide_exact.WideExact.BYTE_LEN : Std.Usize := 32#usize

/-- [aspis_core::field::P]
    Source: '/home/dombarker/project-offloads/codex-cx-prover-dict-20261026/src/crates/aspis-core/src/field.rs', lines 19:0-19:16
    Name pattern: [aspis_core::field::P]
    Visibility: public -/
@[global_simps, irreducible, rust_const "aspis_core::field::P"]
def aspis_core.field.P : Std.U32 := 2147483647#u32

/-- [aspis_core::field::wide_exact::{aspis_core::field::wide_exact::WideExact}::from_limbs]:
    Source: '/home/dombarker/project-offloads/codex-cx-prover-dict-20261026/src/crates/aspis-core/src/field/wide_exact.rs', lines 207:4-207:69
    Name pattern: [aspis_core::field::wide_exact::{aspis_core::field::wide_exact::WideExact}::from_limbs]
    Visibility: public -/
@[rust_fun
  "aspis_core::field::wide_exact::{aspis_core::field::wide_exact::WideExact}::from_limbs"]
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

/-- [aspis_core::field::wide_exact::{aspis_core::field::wide_exact::WideExact}::to_limbs]:
    Source: '/home/dombarker/project-offloads/codex-cx-prover-dict-20261026/src/crates/aspis-core/src/field/wide_exact.rs', lines 238:4-238:58
    Name pattern: [aspis_core::field::wide_exact::{aspis_core::field::wide_exact::WideExact}::to_limbs]
    Visibility: public -/
@[rust_fun
  "aspis_core::field::wide_exact::{aspis_core::field::wide_exact::WideExact}::to_limbs"]
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

/-- [aspis_core::field::wide_exact::{aspis_core::field::wide_exact::WideExact}::from_le_bytes]:
    Source: '/home/dombarker/project-offloads/codex-cx-prover-dict-20261026/src/crates/aspis-core/src/field/wide_exact.rs', lines 255:4-255:54
    Name pattern: [aspis_core::field::wide_exact::{aspis_core::field::wide_exact::WideExact}::from_le_bytes]
    Visibility: public -/
@[rust_fun
  "aspis_core::field::wide_exact::{aspis_core::field::wide_exact::WideExact}::from_le_bytes"]
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



#print axioms aspis_core.field.wide_exact.WideExact.BYTE_LEN
#print axioms aspis_core.field.P
#print axioms aspis_core.field.wide_exact.WideExact.from_limbs
#print axioms aspis_core.field.wide_exact.WideExact.to_limbs
#print axioms aspis_core.field.wide_exact.WideExact.from_le_bytes
end PDict_CodecSource
