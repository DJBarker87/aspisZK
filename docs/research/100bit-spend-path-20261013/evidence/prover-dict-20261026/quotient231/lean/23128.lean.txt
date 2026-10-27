import R1Z.PDict_RemainingCommute231_12
set_option autoImplicit false
noncomputable section
namespace R1Z.PDict_RemainingCommute231
open Aeneas Aeneas.Std Result ProverRwFull
open PDict_RemainingExt231 (replace stage0)
open PDict_Typenum in

theorem stage13 [types : ExternalTypes] (ops other : ExternalFuns) :
    @PDict_Typenum.selected types (@replace types ops other) =
    @replace types (@PDict_Typenum.selected types ops) other := by
  letI : ExternalTypes := types
  let upd (d : @ExternalFuns (types)) : @ExternalFuns (types) :=
    { d with
    op163 := .ok 0#isize,
    op164 := .ok 0#i64,
    op165 := .ok 0#i32,
    op166 := .ok 0#i16,
    op167 := .ok 0#i8,
    op168 := .ok 0#usize,
    op169 := .ok 0#u64,
    op170 := .ok 0#u32,
    op171 := .ok 0#u16,
    op172 := .ok 0#u8,
    op173 := .ok 0#isize,
    op174 := .ok 0#i64,
    op175 := .ok 0#i32,
    op176 := .ok 0#i16,
    op177 := .ok 0#i8,
    op178 := .ok 0#usize,
    op179 := .ok 0#u64,
    op180 := .ok 0#u32,
    op181 := .ok 0#u16,
    op182 := .ok 0#u8,
    op183 := .ok (),
    op184 := fun x => .ok x,
    op188 := .ok true,
    op189 := .ok 1#u8,
    op190 := .ok (),
    op191 := .ok true,
    op192 := .ok 1#u8,
    op193 := .ok (),
    op194 := fun x => .ok x,
    op196 := .ok Ordering.eq,
    op197 := .ok Ordering.gt,
    op198 := .ok false,
    op199 := .ok 0#u8,
    op200 := .ok (),
    op201 := .ok false,
    op202 := .ok 0#u8,
    op203 := .ok (),
    op204 := fun x => .ok x }
  have hu (d : @ExternalFuns (types)) :
      upd (@replace (types) d other) = @replace (types) (upd d) other := by rfl
  change upd (@PDict_WireError.selected types (@replace (types) ops other)) =
    @replace (types) (upd (@PDict_WireError.selected types ops)) other
  exact (congrArg upd (@stage12 types ops other)).trans (hu (@PDict_WireError.selected types ops))

#print axioms stage13
end R1Z.PDict_RemainingCommute231
