import Aeneas
open Aeneas Aeneas.Std Result ControlFlow Error
set_option maxHeartbeats 1000000
namespace NHJ_RouteReference
def admitted_ref (data : Slice Std.U8) : Result Bool := do
  let i := Slice.len data
  if i = 2#usize
  then
    let i1 ← Slice.index_usize data 0#usize
    if i1 = 3#u8
    then
      let i2 ← Slice.index_usize data 1#usize
      if i2 = 10#u8
      then ok true
      else
        if i2 = 11#u8
        then ok true
        else
          let i3 := Slice.len data
          if i3 >= 4#usize
          then
            if i1 = 65#u8
            then
              if i2 = 83#u8
              then
                let i4 ← Slice.index_usize data 2#usize
                if i4 = 81#u8
                then let i5 ← Slice.index_usize data 3#usize
                     ok (i5 = 56#u8)
                else ok false
              else ok false
            else ok false
          else ok false
    else
      let i2 := Slice.len data
      if i2 >= 4#usize
      then
        if i1 = 65#u8
        then
          let i3 ← Slice.index_usize data 1#usize
          if i3 = 83#u8
          then
            let i4 ← Slice.index_usize data 2#usize
            if i4 = 81#u8
            then let i5 ← Slice.index_usize data 3#usize
                 ok (i5 = 56#u8)
            else ok false
          else ok false
        else ok false
      else ok false
  else
    let i1 := Slice.len data
    if i1 >= 4#usize
    then
      let i2 ← Slice.index_usize data 0#usize
      if i2 = 65#u8
      then
        let i3 ← Slice.index_usize data 1#usize
        if i3 = 83#u8
        then
          let i4 ← Slice.index_usize data 2#usize
          if i4 = 81#u8
          then let i5 ← Slice.index_usize data 3#usize
               ok (i5 = 56#u8)
          else ok false
        else ok false
      else ok false
    else ok false

#print Aeneas.Std.Slice.index_usize
end NHJ_RouteReference
