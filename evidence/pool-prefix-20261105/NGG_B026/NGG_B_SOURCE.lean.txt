import NGG_SpineRef.Funs
import NGG_Scalar
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace NGG_LayoutValue
open NGG_SpineRef
def cursor (rollover : Bool) : Usize := if rollover then 5#usize else 4#usize
def expected (rollover withdrawal : Bool) : Usize :=
  if rollover then if withdrawal then 18#usize else 13#usize
  else if withdrawal then 17#usize else 12#usize
def fields (rollover withdrawal : Bool) : Layout :=
  if rollover then
    ⟨5#usize,6#usize,7#usize,8#usize,10#usize,11#usize,
      (if withdrawal then 17#usize else 12#usize),12#usize⟩
  else ⟨4#usize,5#usize,6#usize,7#usize,9#usize,10#usize,
      (if withdrawal then 16#usize else 11#usize),11#usize⟩
def value (rollover withdrawal : Bool) (n : Usize)
    (unique : core.result.Result Unit NGGSpineError) : core.result.Result Layout NGGSpineError :=
  if n != expected rollover withdrawal then
    if n < expected rollover withdrawal then .Err .NotEnoughAccountKeys else .Err .InvalidArgument
  else match unique with | .Err e => .Err e | .Ok _ => .Ok (fields rollover withdrawal)

theorem result (rollover withdrawal : Bool) (n : Usize)
    (unique : core.result.Result Unit NGGSpineError) :
    NGG_SpineRef.layout_tail (cursor rollover) withdrawal n unique =
      ok (value rollover withdrawal n unique) := by
  have a0 : Usize.wrapping_add 4#usize 1#usize = 5#usize := NGG_Scalar.wrapping_add _ _ _ (by rfl)
  have a1 : Usize.wrapping_add 4#usize 2#usize = 6#usize := NGG_Scalar.wrapping_add _ _ _ (by rfl)
  have a2 : Usize.wrapping_add 4#usize 3#usize = 7#usize := NGG_Scalar.wrapping_add _ _ _ (by rfl)
  have a3 : Usize.wrapping_add 4#usize 5#usize = 9#usize := NGG_Scalar.wrapping_add _ _ _ (by rfl)
  have a4 : Usize.wrapping_add 4#usize 6#usize = 10#usize := NGG_Scalar.wrapping_add _ _ _ (by rfl)
  have a5 : Usize.wrapping_add 4#usize 7#usize = 11#usize := NGG_Scalar.wrapping_add _ _ _ (by rfl)
  have a6 : Usize.wrapping_add 5#usize 1#usize = 6#usize := NGG_Scalar.wrapping_add _ _ _ (by rfl)
  have a7 : Usize.wrapping_add 5#usize 2#usize = 7#usize := NGG_Scalar.wrapping_add _ _ _ (by rfl)
  have a8 : Usize.wrapping_add 5#usize 3#usize = 8#usize := NGG_Scalar.wrapping_add _ _ _ (by rfl)
  have a9 : Usize.wrapping_add 5#usize 5#usize = 10#usize := NGG_Scalar.wrapping_add _ _ _ (by rfl)
  have a10 : Usize.wrapping_add 5#usize 6#usize = 11#usize := NGG_Scalar.wrapping_add _ _ _ (by rfl)
  have a11 : Usize.wrapping_add 5#usize 7#usize = 12#usize := NGG_Scalar.wrapping_add _ _ _ (by rfl)
  have a12 : Usize.wrapping_add 11#usize 0#usize = 11#usize := NGG_Scalar.wrapping_add _ _ _ (by rfl)
  have a13 : Usize.wrapping_add 11#usize 1#usize = 12#usize := NGG_Scalar.wrapping_add _ _ _ (by rfl)
  have a14 : Usize.wrapping_add 11#usize 5#usize = 16#usize := NGG_Scalar.wrapping_add _ _ _ (by rfl)
  have a15 : Usize.wrapping_add 12#usize 0#usize = 12#usize := NGG_Scalar.wrapping_add _ _ _ (by rfl)
  have a16 : Usize.wrapping_add 12#usize 1#usize = 13#usize := NGG_Scalar.wrapping_add _ _ _ (by rfl)
  have a17 : Usize.wrapping_add 12#usize 5#usize = 17#usize := NGG_Scalar.wrapping_add _ _ _ (by rfl)
  have a18 : Usize.wrapping_add 16#usize 1#usize = 17#usize := NGG_Scalar.wrapping_add _ _ _ (by rfl)
  have a19 : Usize.wrapping_add 17#usize 1#usize = 18#usize := NGG_Scalar.wrapping_add _ _ _ (by rfl)
  have c0 : Usize.checked_add 11#usize 0#usize = some 11#usize := NGG_Scalar.checked_add _ _ _ (by rfl)
  have c1 : Usize.checked_add 11#usize 5#usize = some 16#usize := NGG_Scalar.checked_add _ _ _ (by rfl)
  have c2 : Usize.checked_add 12#usize 0#usize = some 12#usize := NGG_Scalar.checked_add _ _ _ (by rfl)
  have c3 : Usize.checked_add 12#usize 5#usize = some 17#usize := NGG_Scalar.checked_add _ _ _ (by rfl)
  cases rollover <;> cases withdrawal <;> cases unique <;>
    simp [NGG_SpineRef.layout_tail,cursor,expected,fields,value,lift,
      NGG_SpineRef.core.option.Option.ok_or,
      core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
      a0,a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14,a15,a16,a17,a18,a19,c0,c1,c2,c3] <;> split_ifs <;> simp_all
#print axioms result
end NGG_LayoutValue
