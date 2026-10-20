import AspisR1GroupedPairCut.Funs
import CurrentWideLinearExact

set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow

namespace AspisR1GroupedPairCut.Proofs.RealAddCurrent

abbrev S := AspisR1GroupedPairCut.field.WideExact
abbrev E := AspisR1CurrentWide.Proof.E

def toCM (x : AspisR1GroupedPairCut.field.CM31) : AspisR1CurrentWide.field.CM31 := ⟨x.a,x.b⟩
def toQM (x : AspisR1GroupedPairCut.field.QM31) : AspisR1CurrentWide.field.QM31 := ⟨toCM x.c0,toCM x.c1⟩
def toE (x : S) : E := ⟨toQM x.c0,toQM x.c1⟩
def fromCM (x : AspisR1CurrentWide.field.CM31) : AspisR1GroupedPairCut.field.CM31 := ⟨x.a,x.b⟩
def fromQM (x : AspisR1CurrentWide.field.QM31) : AspisR1GroupedPairCut.field.QM31 := ⟨fromCM x.c0,fromCM x.c1⟩
def fromE (x : E) : S := ⟨fromQM x.c0,fromQM x.c1⟩

theorem to_from (x : E) : toE (fromE x) = x := by cases x <;> rfl
theorem from_to (x : S) : fromE (toE x) = x := by cases x <;> rfl

def Canonical (x : S) : Prop := AspisR1CurrentWide.Proof.CanonicalWide (toE x)
def decode (x : S) := AspisR1CurrentWide.Proof.decodeWide (toE x)
def add (x y : S) : Result S := do
  let z ← AspisR1CurrentWide.field.wide_exact.WideExact.add (toE x) (toE y)
  ok (fromE z)

theorem add_total_exact (x y : S) (hx : Canonical x) (hy : Canonical y) :
    ∃ z, add x y = .ok z ∧ Canonical z ∧ decode z = decode x + decode y := by
  obtain ⟨z,hz,hc,he⟩ := AspisR1CurrentWide.Proof.wide_add_total_exact (toE x) (toE y) hx hy
  refine ⟨fromE z, ?_, ?_, ?_⟩
  · simp only [add,hz,bind_tc_ok]
  · simpa only [Canonical,to_from] using hc
  · simpa only [decode,to_from] using he

def ops (mulOp : S → S → Result S) : AspisR1GroupedPairCut.weights.WideExactOps := ⟨add,mulOp⟩
end AspisR1GroupedPairCut.Proofs.RealAddCurrent

#print axioms AspisR1GroupedPairCut.Proofs.RealAddCurrent.add_total_exact
