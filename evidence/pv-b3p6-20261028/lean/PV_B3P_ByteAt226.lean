import PV_B3P_ByteField226
open Aeneas Aeneas.Std Result ControlFlow Error
set_option maxRecDepth 2048
set_option maxHeartbeats 1000000
namespace PV_B3P_226
def reference226.byte_at
  (p : reference226.OwnedPublic) (i : Std.Usize) :
  Result (core.result.Result Std.U8 aspis_core.state_only_prefix.r0.Error)
  := do
  let (b, n) ←
    if p.withdrawal
    then ok (true, 1427#usize)
    else ok (false, 1455#usize)
  if i >= n
  then ok (core.result.Result.Ok 0#u8)
  else
    if i = 0#usize
    then
      if b
      then ok (core.result.Result.Ok 1#u8)
      else ok (core.result.Result.Ok 0#u8)
    else
      if i < 33#usize
      then
        let i1 ← lift (Std.Usize.wrapping_sub i 1#usize)
        let i2 ← i1 / 4#usize
        let i3 ← Array.index_usize p.anchor i2
        let i4 ← lift (Std.Usize.wrapping_sub i 1#usize)
        let i5 ← i4 % 4#usize
        reference226.field_byte i3 i5
      else
        if i < 65#usize
        then
          let i1 ← lift (Std.Usize.wrapping_sub i 33#usize)
          let i2 ← i1 / 4#usize
          let i3 ← Array.index_usize p.nullifier i2
          let i4 ← lift (Std.Usize.wrapping_sub i 33#usize)
          let i5 ← i4 % 4#usize
          reference226.field_byte i3 i5
        else
          if i < 69#usize
          then
            let i1 ← lift (Std.Usize.wrapping_sub i 65#usize)
            reference226.field_byte p.asset_id i1
          else
            if i = 69#usize
            then
              if b
              then ok (core.result.Result.Ok 0#u8)
              else ok (core.result.Result.Ok 1#u8)
            else
              let change ← if b
                             then ok 70#usize
                             else ok 102#usize
              if i < change
              then
                let i1 ← lift (Std.Usize.wrapping_sub i 70#usize)
                let i2 ← i1 / 4#usize
                let i3 ← Array.index_usize p.recipient i2
                let i4 ← lift (Std.Usize.wrapping_sub i 70#usize)
                let i5 ← i4 % 4#usize
                reference226.field_byte i3 i5
              else
                let i1 ← lift (Std.Usize.wrapping_add change 32#usize)
                if i < i1
                then
                  let i2 ← lift (Std.Usize.wrapping_sub i change)
                  let i3 ← i2 / 4#usize
                  let i4 ← Array.index_usize p.change i3
                  let i5 ← lift (Std.Usize.wrapping_sub i change)
                  let i6 ← i5 % 4#usize
                  reference226.field_byte i4 i6
                else
                  let i2 ← lift (Std.Usize.wrapping_add change 32#usize)
                  if i = i2
                  then
                    if b
                    then ok (core.result.Result.Ok 1#u8)
                    else ok (core.result.Result.Ok 0#u8)
                  else
                    let index ← if b
                                  then ok 107#usize
                                  else ok 135#usize
                    if i < index
                    then
                      let i3 ← lift (Std.Usize.wrapping_add change 33#usize)
                      let i4 ← lift (Std.Usize.wrapping_sub i i3)
                      reference226.field_byte p.withdrawal_amount i4
                    else
                      let i3 ← lift (Std.Usize.wrapping_add index 8#usize)
                      if i < i3
                      then
                        let i4 ← lift (Std.Usize.wrapping_sub i index)
                        let i5 ← lift (UScalar.cast .U32 i4)
                        let i6 ← lift (Std.U32.wrapping_mul 8#u32 i5)
                        let i7 ←
                          lift (Std.U64.wrapping_shr p.next_pair_index i6)
                        let i8 ← lift (UScalar.cast .U8 i7)
                        ok (core.result.Result.Ok i8)
                      else
                        let front ←
                          lift (Std.Usize.wrapping_add index 8#usize)
                        let i4 ←
                          lift (Std.Usize.wrapping_add front 640#usize)
                        if i < i4
                        then
                          let j ← lift (Std.Usize.wrapping_sub i front)
                          let i5 ← j / 32#usize
                          let i6 ← j % 32#usize
                          let i7 ← i6 / 4#usize
                          let a ← Array.index_usize p.frontier i5
                          let i8 ← Array.index_usize a i7
                          let i9 ← j % 4#usize
                          reference226.field_byte i8 i9
                        else
                          let i5 ←
                            lift (Std.Usize.wrapping_add front 672#usize)
                          if i < i5
                          then
                            let i6 ← lift (Std.Usize.wrapping_sub i front)
                            let j ←
                              lift (Std.Usize.wrapping_sub i6 640#usize)
                            let i7 ← j / 4#usize
                            let i8 ← Array.index_usize p.next_root i7
                            let i9 ← j % 4#usize
                            reference226.field_byte i8 i9
                          else
                            let i6 ← lift (Std.Usize.wrapping_sub i front)
                            let j ←
                              lift (Std.Usize.wrapping_sub i6 672#usize)
                            let i7 ← j / 32#usize
                            let i8 ← j % 32#usize
                            let i9 ← i8 / 4#usize
                            let a ← Array.index_usize p.next_frontier i7
                            let i10 ← Array.index_usize a i9
                            let i11 ← j % 4#usize
                            reference226.field_byte i10 i11


end PV_B3P_226
#print axioms PV_B3P_226.reference226.byte_at
