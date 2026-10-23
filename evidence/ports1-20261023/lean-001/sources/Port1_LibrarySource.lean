import VTop_Model

/-! Exact no-digest library bodies on the extracted stage carriers. The strict
unrolled decoder is the retained generated body with only carrier identifiers
relocated; the source audit records the source and generated inputs. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.Port1_LibrarySource
open Aeneas Aeneas.Std Result VTop_Stages

def fromLimbs
  (limbs : Array Std.U32 8#usize) :
  Result (Option aspis_core.field.wide_exact.WideExact)
  := do
  let i ← Array.index_usize limbs 0#usize
  if i >= 2147483647#u32
  then ok none
  else
    let i1 ← Array.index_usize limbs 1#usize
    if i1 >= 2147483647#u32
    then ok none
    else
      let i2 ← Array.index_usize limbs 2#usize
      if i2 >= 2147483647#u32
      then ok none
      else
        let i3 ← Array.index_usize limbs 3#usize
        if i3 >= 2147483647#u32
        then ok none
        else
          let i4 ← Array.index_usize limbs 4#usize
          if i4 >= 2147483647#u32
          then ok none
          else
            let i5 ← Array.index_usize limbs 5#usize
            if i5 >= 2147483647#u32
            then ok none
            else
              let i6 ← Array.index_usize limbs 6#usize
              if i6 >= 2147483647#u32
              then ok none
              else
                let i7 ← Array.index_usize limbs 7#usize
                if i7 >= 2147483647#u32
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

/-- [aspis_core::field::wide_exact::{aspis_core::field::wide_exact::WideExact}::from_le_bytes]:
    Source: 'field/wide_exact.rs', lines 255:4-270:5
    Visibility: public -/
def decode
  (bytes : Slice Std.U8) : Result (Option aspis_core.field.wide_exact.WideExact) := do
  let i := Slice.len bytes
  if i != 32#usize
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
    fromLimbs
      (Array.make 8#usize [ i5, i10, i15, i20, i25, i30, i35, i40 ])


def zero : aspis_core.field.wide_exact.WideExact :=
  ⟨⟨⟨0#u32,0#u32⟩,⟨0#u32,0#u32⟩⟩,⟨⟨0#u32,0#u32⟩,⟨0#u32,0#u32⟩⟩⟩

def okOr {T E : Type} (value : Option T) (error : E) : Result (core.result.Result T E) :=
  .ok (match value with | some x => .Ok x | none => .Err error)

def mark (observer : Option (verifier.Phase → Result Unit)) (phase : verifier.Phase) : Result Unit :=
  match observer with | none => .ok () | some f => f phase

/-- Only the successful array conversion is consumed on accepted stage paths.
The error branch represents Rust unwrap's panic, without a Debug formatter. -/
def unwrap32 (value : core.result.Result (Array U8 32#usize) core.array.TryFromSliceError) :
    Result (Array U8 32#usize) :=
  match value with | .Ok x => .ok x | .Err _ => .fail .panic

theorem mark_none (phase : verifier.Phase) : mark none phase = .ok () := rfl

#print axioms fromLimbs
#print axioms decode
#print axioms zero
#print axioms okOr
#print axioms mark
#print axioms unwrap32
#print axioms mark_none
end AspisR1.Port1_LibrarySource
end
