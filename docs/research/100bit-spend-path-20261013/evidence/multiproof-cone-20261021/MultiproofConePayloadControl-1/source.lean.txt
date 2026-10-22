import MultiproofConeLogicalPayload

set_option autoImplicit false
namespace AspisR1.MultiproofConePayloadControl
open Aeneas Aeneas.Std Result
open MultiproofParserRef MultiproofConeLogicalPayload

/-- Factor precisely the duplicated payload branch emitted by Aeneas. The
continuation contains frame allocation, accumulator push and row recursion. -/
theorem inline_eq {α : Type} (row : U8) (payload : Slice U8)
    (k : alloc.vec.Vec U8 → Result (Option α)) :
    (if row>=14#u8 then do
      let good ← reference.check_values payload
      if good then
        if row>=14#u8 then do
          let o ← reference.expand_rows payload (alloc.vec.Vec.new U8)
          match o with
          | none => ok none
          | some logical => k logical
        else do
          let logical ← alloc.slice.Slice.to_vec core.clone.CloneU8 payload
          k logical
      else ok none
    else
      if row>=14#u8 then do
        let o ← reference.expand_rows payload (alloc.vec.Vec.new U8)
        match o with
        | none => ok none
        | some logical => k logical
      else do
        let logical ← alloc.slice.Slice.to_vec core.clone.CloneU8 payload
        k logical) =
    (do let o ← prepare row payload
        match o with
        | none => ok none
        | some logical => k logical) := by
  unfold prepare
  by_cases compact : row>=14#u8
  · simp only [compact,if_true]
    cases hc : reference.check_values payload with
    | fail e => rfl
    | div => rfl
    | ok flag =>
      cases flag with
      | false => rfl
      | true =>
        cases he : reference.expand_rows payload (alloc.vec.Vec.new U8) with
        | fail e => rfl
        | div => rfl
        | ok result => cases result <;> rfl
  · simp only [compact,if_false]
    cases ht : alloc.slice.Slice.to_vec core.clone.CloneU8 payload <;> rfl

#print axioms inline_eq
end AspisR1.MultiproofConePayloadControl
