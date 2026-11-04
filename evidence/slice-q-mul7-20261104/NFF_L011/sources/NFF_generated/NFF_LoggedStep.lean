import NFF_ReadDomains
import NFE_NFA_InnerStep
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace AspisR1.NFF_LoggedStep
open Aeneas Aeneas.Std Result ControlFlow

def update (oracle : NFF_LoggedEight.Oracle) (g : NEV_DotInputs.Coefficients)
    (term : Usize) (scalar : U32) (sums : Array U64 8#usize) : Result (Array U64 8#usize) := do
  let value ← Array.index_usize g term
  let coefficient ← FIo_Native.aspis_core.field.wide_exact.WideExact.to_limbs value
  NFF_LoggedEight.eight oracle coefficient scalar sums

theorem update_replay (oracle : NFF_LoggedEight.Oracle) (law : NFF_LoggedEight.Law oracle)
    (g : NEV_DotInputs.Coefficients) (domain : NEV_DotInputs.Canonical g)
    (term : Usize) (inside : term.val<26) (scalar : U32)
    (hs : scalar.val<NEG_DotDomain.P) (sums : Array U64 8#usize) :
    update oracle g term scalar sums=NEV_ActualDotStep.update g term scalar sums := by
  obtain ⟨value,coefficient,read,project,canonical⟩:=NFF_ReadDomains.selected g domain term inside
  rw [NFE_NEV_DotEight.suffix]
  simp only [update,read,project,bind_tc_ok,
    NFF_LoggedEight.replay oracle law coefficient canonical scalar hs]

def step (oracle : NFF_LoggedEight.Oracle) (q : Array U8 608#usize)
    (g : NEV_DotInputs.Coefficients) (slot : Usize)
    (iter : core.ops.range.Range Usize) (sums : Array U64 8#usize) :
    Result (ControlFlow (core.ops.range.Range Usize × Array U64 8#usize) (Array U64 8#usize)) := do
  let (o,next) ← core.iter.range.IteratorRange.next core.iter.range.StepUsize iter
  match o with
  | none => ok (done sums)
  | some term => do
    let scalar ← NEV_DotRead.read q slot term
    let out ← update oracle g term scalar sums
    ok (cont (next,out))

/-- Every active native-model iteration agrees, including read rejection or
panic. Canonicality is derived at the reached parser, not postulated per child. -/
theorem active (oracle : NFF_LoggedEight.Oracle) (law : NFF_LoggedEight.Law oracle)
    (q : Array U8 608#usize) (g : NEV_DotInputs.Coefficients)
    (domain : NEV_DotInputs.Canonical g) (slot : Usize)
    (iter : core.ops.range.Range Usize) (sums : Array U64 8#usize)
    (inside : iter.start.val < iter.end.val) (endpoint : iter.end.val≤26) :
    step oracle q g slot iter sums=
      FIp_NativeDots.fast_dots.four_dots_one_loop0_loop0.body q g slot iter sums := by
  obtain ⟨⟨o,cursor⟩,advance,value,start,finish⟩:=WP.spec_imp_exists
    (core.iter.range.IteratorRange.next_UScalar_some_spec
      (ty:=.Usize) (cloneInst:=core.clone.CloneUsize)
      (partialOrdInst:=core.cmp.PartialOrdUsize) (by intro x;rfl) (by intro x y;rfl)
      iter inside)
  subst o
  rw [NEV_ActualDotStep.body]
  simp only [step,NEV_ActualDotStep.step,advance,bind_tc_ok]
  cases read : NEV_DotRead.read q slot iter.start with
  | fail e => simp only [read,bind_tc_fail]
  | div => simp only [read,bind_tc_div]
  | ok scalar =>
    have hs:=NEV_DotReadDomain.reached q slot iter.start scalar read
    simp only [read,bind_tc_ok,update_replay oracle law g domain iter.start (by omega) scalar hs]

#print axioms update_replay
#print axioms active
end AspisR1.NFF_LoggedStep
end
