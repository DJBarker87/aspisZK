import AspisR1S9HelperP6.Funs
import CurrentWideLinearExact
import CurrentWideMulM31V13

set_option autoImplicit false
open Aeneas Aeneas.Std Result

namespace AspisR1S9CurrentFieldOpsV1

abbrev S := AspisR1S9HelperP6.field.WideExact
abbrev E := AspisR1CurrentWide.Proof.E
abbrev M := AspisR1S9HelperP6.field.M31

private def toCM (x : AspisR1S9HelperP6.field.CM31) : AspisR1CurrentWide.field.CM31 := ⟨x.a,x.b⟩
private def toQM (x : AspisR1S9HelperP6.field.QM31) : AspisR1CurrentWide.field.QM31 := ⟨toCM x.c0,toCM x.c1⟩
def toE (x : S) : E := ⟨toQM x.c0,toQM x.c1⟩
private def fromCM (x : AspisR1CurrentWide.field.CM31) : AspisR1S9HelperP6.field.CM31 := ⟨x.a,x.b⟩
private def fromQM (x : AspisR1CurrentWide.field.QM31) : AspisR1S9HelperP6.field.QM31 := ⟨fromCM x.c0,fromCM x.c1⟩
def fromE (x : E) : S := ⟨fromQM x.c0,fromQM x.c1⟩

theorem to_from (x : E) : toE (fromE x) = x := by cases x <;> rfl
theorem from_to (x : S) : fromE (toE x) = x := by cases x <;> rfl

def Canonical (x : S) : Prop := AspisR1CurrentWide.Proof.CanonicalWide (toE x)
def decode (x : S) := AspisR1CurrentWide.Proof.decodeWide (toE x)

def actualWideAdd (x y : S) : Result S := do
  let z ← AspisR1CurrentWide.field.wide_exact.WideExact.add (toE x) (toE y)
  ok (fromE z)

def actualWideMulM31 (x : S) (s : M) : Result S := do
  let z ← AspisR1CurrentWide.field.wide_exact.WideExact.mul_m31 (toE x) s
  ok (fromE z)

def installWideAdd (ops : AspisR1S9HelperP6.FieldOps) : AspisR1S9HelperP6.FieldOps :=
  { ops with wideAdd := actualWideAdd }

def installWideAddMulM31 (ops : AspisR1S9HelperP6.FieldOps) : AspisR1S9HelperP6.FieldOps :=
  { (installWideAdd ops) with wideMulM31 := actualWideMulM31 }

theorem actualWideAdd_total_exact (x y : S) (hx : Canonical x) (hy : Canonical y) :
    ∃ z, actualWideAdd x y = .ok z ∧ Canonical z ∧ decode z = decode x + decode y := by
  obtain ⟨z,hz,hc,hv⟩ := AspisR1CurrentWide.Proof.wide_add_total_exact (toE x) (toE y) hx hy
  refine ⟨fromE z, ?_, ?_, ?_⟩
  · simp only [actualWideAdd,hz,bind_tc_ok]
  · change AspisR1CurrentWide.Proof.CanonicalWide (toE (fromE z))
    rw [to_from]
    exact hc
  · change AspisR1CurrentWide.Proof.decodeWide (toE (fromE z)) = _
    rw [to_from]
    exact hv

private theorem bind_ok_inv {α β : Type} {r : Result α} {f : α → Result β}
    {x : β} (h : Bind.bind r f = .ok x) :
    ∃ a, r = .ok a ∧ f a = .ok x := by
  cases r with
  | ok a => exact ⟨a,rfl,h⟩
  | fail e => simp [Bind.bind] at h
  | div => simp [Bind.bind] at h

theorem actualWideMulM31_success (x z : S) (s : M)
    (hx : Canonical x)
    (h : actualWideMulM31 x s = .ok z) :
    Canonical z ∧ decode z = decode x * AspisR1CurrentWide.Proof.wideScalarEmbedding s := by
  unfold actualWideMulM31 at h
  rcases bind_ok_inv h with ⟨w,hw,h⟩
  have he : fromE w = z := Result.ok.inj h
  subst z
  obtain ⟨hc,hv⟩ := AspisR1CurrentWide.Proof.wide_mul_m31_success (toE x) w s hx hw
  constructor
  · change AspisR1CurrentWide.Proof.CanonicalWide (toE (fromE w))
    rw [to_from]
    exact hc
  · change AspisR1CurrentWide.Proof.decodeWide (toE (fromE w)) = _
    rw [to_from]
    exact hv

theorem installedWideAdd_dispatch (ops : AspisR1S9HelperP6.FieldOps) (x y : S) :
    (letI : AspisR1S9HelperP6.FieldOps := installWideAdd ops
     AspisR1S9HelperP6.field.WideExact.add x y) = actualWideAdd x y := by
  rfl

theorem installedWideMulM31_dispatch (ops : AspisR1S9HelperP6.FieldOps) (x : S) (s : M) :
    (letI : AspisR1S9HelperP6.FieldOps := installWideAddMulM31 ops
     AspisR1S9HelperP6.field.WideExact.mul_m31 x s) = actualWideMulM31 x s := by
  rfl

#print axioms actualWideAdd_total_exact
#print axioms actualWideMulM31_success
#print axioms installedWideAdd_dispatch
#print axioms installedWideMulM31_dispatch

end AspisR1S9CurrentFieldOpsV1
