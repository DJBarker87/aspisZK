import CuSavingsRetainedCompositionDots
import CuSavingsCanonicalDotsInvariant
set_option autoImplicit false
namespace AspisR1.CuSavingsRetainedDotsBinding
open Aeneas Aeneas.Std Result AspisR1RetainedDots
namespace D
abbrev Old := AspisR1CanonicalDots.old_pairing.EbyKDot
abbrev New := AspisR1CanonicalDots.new_pairing.EbyKDot
abbrev E := AspisR1CanonicalDots.field.wide_exact.WideExact
abbrev K := AspisR1CanonicalDots.field.QM31
end D
abbrev E := field.wide_exact.WideExact
abbrev K := field.QM31
abbrev Dot := fast_pairing.EbyKDot

def toK (x : K) : D.K := ⟨⟨x.c0.a,x.c0.b⟩,⟨x.c1.a,x.c1.b⟩⟩
def toE (x : E) : D.E := ⟨toK x.c0,toK x.c1⟩
def fromK (x : D.K) : K := ⟨⟨x.c0.a,x.c0.b⟩,⟨x.c1.a,x.c1.b⟩⟩
def fromE (x : D.E) : E := ⟨fromK x.c0,fromK x.c1⟩
def toNew (x : Dot) : D.New := ⟨⟨x.c0.sums⟩,⟨x.c1.sums⟩,x.count⟩
def fromNew (x : D.New) : Dot := ⟨⟨x.c0.sums⟩,⟨x.c1.sums⟩,x.count⟩
/-- Reconstruct erased private counters from the source public counter. -/
def toOld (x : Dot) : D.Old := ⟨⟨x.c0.sums,x.count⟩,⟨x.c1.sums,x.count⟩,x.count⟩
def fromOld (x : D.Old) : Dot := ⟨⟨x.c0.sums⟩,⟨x.c1.sums⟩,x.count⟩

variable [AspisR1CanonicalDots.Shared]
def newDot : Result Dot := do
  let x ← AspisR1CanonicalDots.new_pairing.EbyKDot.new
  .ok (fromNew x)
def oldDot : Result Dot := do
  let x ← AspisR1CanonicalDots.old_pairing.EbyKDot.new
  .ok (fromOld x)
def newPush (state : Dot) (value : E) (scalar : K) :
    Result (core.result.Result Unit Unit × Dot) := do
  let (r,after) ← AspisR1CanonicalDots.new_pairing.EbyKDot.push (toNew state) (toE value) (toK scalar)
  .ok (r,fromNew after)
def oldPush (state : Dot) (value : E) (scalar : K) :
    Result (core.result.Result Unit Unit × Dot) := do
  let (r,after) ← AspisR1CanonicalDots.old_pairing.EbyKDot.push (toOld state) (toE value) (toK scalar)
  .ok (r,fromOld after)
def newFinish (state : Dot) : Result E := do
  let out ← AspisR1CanonicalDots.new_pairing.EbyKDot.finish (toNew state)
  .ok (fromE out)
def oldFinish (state : Dot) : Result E := do
  let out ← AspisR1CanonicalDots.old_pairing.EbyKDot.finish (toOld state)
  .ok (fromE out)
@[reducible] def newShared (common : Shared) : Shared :=
  {common with newDot:=newDot,push:=newPush,finish:=newFinish}
@[reducible] def oldShared (common : Shared) : Shared :=
  {common with newDot:=oldDot,push:=oldPush,finish:=oldFinish}

theorem initializer : newDot=oldDot := rfl

theorem push_equivalence (state : Dot) (value : E) (scalar : K)
    (hc : CuSavingsCanonicalDotsField.WideCanonical (toE value)) :
    newPush state value scalar=oldPush state value scalar := by
  unfold newPush oldPush
  have hp : toNew state=CuSavingsCanonicalDotsPush.project (toOld state) := rfl
  rw [hp,CuSavingsCanonicalDotsPush.public_push (toOld state) (toE value) (toK scalar) hc ⟨rfl,rfl⟩]
  simp only [bind_assoc_eq,bind_tc_ok,uncurry_apply_pair]
  rfl

theorem finalizer (state : Dot) : newFinish state=oldFinish state := by
  unfold newFinish oldFinish
  rw [CuSavingsCanonicalDotsFinish.new_public_finish,CuSavingsCanonicalDotsFinish.old_public_finish]
  rfl

#print axioms initializer
#print axioms push_equivalence
#print axioms finalizer
end AspisR1.CuSavingsRetainedDotsBinding
