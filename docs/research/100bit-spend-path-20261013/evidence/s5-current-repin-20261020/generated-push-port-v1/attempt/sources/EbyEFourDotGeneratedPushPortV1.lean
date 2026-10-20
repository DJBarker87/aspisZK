import AspisR1EbyEFourDotSourceStepV1

set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow Error

namespace AspisR1EbyEFourDotGeneratedPushPortV1

open AspisR1EbyEFourDotSourceStepV1

/-- Exact Aeneas bind/branch sequence of the selected `EbyEDot.push` body,
with only its three effectful callees exposed as parameters. The parameter
`maxTerm` corresponds to the extracted `MAX_TERMS` constant. -/
def emittedPushParameterized
    (maxTerm : Usize)
    (fromWide : Wide → Result (Array Q 2#usize))
    (pushDot : Dot → Q → Q → Result Dot)
    (addUsize : Usize → Usize → Result Usize)
    (self : State) (left right : Wide) :
    Result ((core.result.Result Unit Unit) × State) := do
  if self.count >= maxTerm
  then ok (core.result.Result.Err (), self)
  else
    let a ← fromWide left
    let a1 ← Array.index_usize a 0#usize
    let b ← Array.index_usize a 1#usize
    let a2 ← fromWide right
    let c ← Array.index_usize a2 0#usize
    let d ← Array.index_usize a2 1#usize
    let d1 ← pushDot self.ac a1 c
    let d2 ← pushDot self.bd b d
    let d3 ← pushDot self.ad a1 d
    let d4 ← pushDot self.bc b c
    let i ← addUsize self.count 1#usize
    ok (core.result.Result.Ok (),
      { ac := d1, bd := d2, ad := d3, bc := d4, count := i })

theorem emittedPushParameterized_eq_sourceSchedule
    (fromWide : Wide → Result (Array Q 2#usize))
    (pushDot : Dot → Q → Q → Result Dot)
    (addUsize : Usize → Usize → Result Usize)
    (self : State) (left right : Wide) :
    emittedPushParameterized maxTerms fromWide pushDot addUsize self left right =
      pushWithOps fromWide pushDot addUsize self left right := rfl

#print axioms emittedPushParameterized_eq_sourceSchedule

end AspisR1EbyEFourDotGeneratedPushPortV1
