import CurrentWideLinearExact
import AspisR1FastDotsCurrent.FunsOpsV4
set_option autoImplicit false
open Aeneas Aeneas.Std Result AspisR1FastDotsCurrent
namespace AspisR1FastDotsTailWideAddCurrentV1
abbrev S4Wide := AspisR1FastDotsCurrent.aspis_core.field.wide_exact.WideExact
abbrev CurrentE := AspisR1CurrentWide.Proof.E
abbrev Ops := AspisR1FastDotsCurrent.FourDotsOps

def s4ToCurrentCM (x : AspisR1FastDotsCurrent.aspis_core.field.CM31) : AspisR1CurrentWide.field.CM31 :=
  {a:=x.a,b:=x.b}
def s4ToCurrentQM (x : AspisR1FastDotsCurrent.aspis_core.field.QM31) : AspisR1CurrentWide.field.QM31 :=
  {c0:=s4ToCurrentCM x.c0,c1:=s4ToCurrentCM x.c1}
def s4ToCurrentE (x : S4Wide) : CurrentE :=
  {c0:=s4ToCurrentQM x.c0,c1:=s4ToCurrentQM x.c1}

def currentToS4CM (x : AspisR1CurrentWide.field.CM31) : AspisR1FastDotsCurrent.aspis_core.field.CM31 :=
  {a:=x.a,b:=x.b}
def currentToS4QM (x : AspisR1CurrentWide.field.QM31) : AspisR1FastDotsCurrent.aspis_core.field.QM31 :=
  {c0:=currentToS4CM x.c0,c1:=currentToS4CM x.c1}
def currentToS4E (x : CurrentE) : S4Wide :=
  {c0:=currentToS4QM x.c0,c1:=currentToS4QM x.c1}

theorem s4ToCurrentE_currentToS4E (x : CurrentE) : s4ToCurrentE (currentToS4E x) = x := by
  cases x
  rfl

theorem currentToS4E_s4ToCurrentE (x : S4Wide) : currentToS4E (s4ToCurrentE x) = x := by
  cases x
  rfl

def currentWideAddS4 (x y : S4Wide) : Result S4Wide := do
  let z ← AspisR1CurrentWide.field.wide_exact.WideExact.add (s4ToCurrentE x) (s4ToCurrentE y)
  ok (currentToS4E z)

def withCurrentWideAdd (ops : Ops) : Ops :=
  {ops with wideAdd := currentWideAddS4}

theorem withCurrentWideAdd_binding (ops : Ops) (x y : S4Wide) :
    (withCurrentWideAdd ops).wideAdd x y = currentWideAddS4 x y := rfl

theorem currentWideAddS4_total_exact (x y : S4Wide)
    (hx : AspisR1CurrentWide.Proof.CanonicalWide (s4ToCurrentE x))
    (hy : AspisR1CurrentWide.Proof.CanonicalWide (s4ToCurrentE y)) :
    ∃ z, currentWideAddS4 x y = .ok z ∧
      AspisR1CurrentWide.Proof.CanonicalWide (s4ToCurrentE z) ∧
      AspisR1CurrentWide.Proof.decodeWide (s4ToCurrentE z) =
        AspisR1CurrentWide.Proof.decodeWide (s4ToCurrentE x) +
        AspisR1CurrentWide.Proof.decodeWide (s4ToCurrentE y) := by
  obtain ⟨z,hz,hcan,heq⟩ := AspisR1CurrentWide.Proof.wide_add_total_exact
    (s4ToCurrentE x) (s4ToCurrentE y) hx hy
  refine ⟨currentToS4E z, ?_, ?_, ?_⟩
  · simp only [currentWideAddS4,hz,bind_tc_ok]
  · simpa only [s4ToCurrentE_currentToS4E] using hcan
  · simpa only [s4ToCurrentE_currentToS4E] using heq

theorem installed_wideAdd_success_exact (ops : Ops) (x y z : S4Wide)
    (hx : AspisR1CurrentWide.Proof.CanonicalWide (s4ToCurrentE x))
    (hy : AspisR1CurrentWide.Proof.CanonicalWide (s4ToCurrentE y))
    (h : (withCurrentWideAdd ops).wideAdd x y = .ok z) :
    AspisR1CurrentWide.Proof.CanonicalWide (s4ToCurrentE z) ∧
    AspisR1CurrentWide.Proof.decodeWide (s4ToCurrentE z) =
      AspisR1CurrentWide.Proof.decodeWide (s4ToCurrentE x) +
      AspisR1CurrentWide.Proof.decodeWide (s4ToCurrentE y) := by
  obtain ⟨out,hout,hcan,heq⟩ := currentWideAddS4_total_exact x y hx hy
  have hout' : currentWideAddS4 x y = .ok z := by
    rw [withCurrentWideAdd_binding] at h
    exact h
  have hz : out = z := Result.ok.inj (hout.symm.trans hout')
  simpa only [hz] using And.intro hcan heq

#print axioms currentWideAddS4_total_exact
#print axioms installed_wideAdd_success_exact
end AspisR1FastDotsTailWideAddCurrentV1
