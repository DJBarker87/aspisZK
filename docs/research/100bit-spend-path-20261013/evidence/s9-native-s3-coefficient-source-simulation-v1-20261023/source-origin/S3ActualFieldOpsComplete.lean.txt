import AspisR1GroupedPairActualFieldOpsV3.Funs
import CurrentWideLinearExact
import CurrentFinishField
open Aeneas Aeneas.Std Result

namespace AspisR1GroupedPairActualFieldOpsV3
namespace ActualFieldComplete

abbrev S := field.WideExact
abbrev E := AspisR1CurrentWide.Proof.E
abbrev FinishE := AspisR1CurrentWide.Proof.FinishE

def toCM (x : field.CM31) : AspisR1CurrentWide.field.CM31 := ⟨x.a, x.b⟩
def toQM (x : field.QM31) : AspisR1CurrentWide.field.QM31 := ⟨toCM x.c0, toCM x.c1⟩
def toE (x : S) : E := ⟨toQM x.c0, toQM x.c1⟩
def fromCM (x : AspisR1CurrentWide.field.CM31) : field.CM31 := ⟨x.a, x.b⟩
def fromQM (x : AspisR1CurrentWide.field.QM31) : field.QM31 := ⟨fromCM x.c0, fromCM x.c1⟩
def fromE (x : E) : S := ⟨fromQM x.c0, fromQM x.c1⟩

theorem to_from (x : E) : toE (fromE x) = x := by cases x <;> rfl
theorem from_to (x : S) : fromE (toE x) = x := by cases x <;> rfl

def Canonical (x : S) : Prop := AspisR1CurrentWide.Proof.CanonicalWide (toE x)
def decode (x : S) : AspisWideTower.WideExact :=
  AspisR1CurrentWide.Proof.decodeWide (toE x)

def finishToS (x : FinishE) : S := fromE (AspisR1CurrentWide.Proof.ofFinishE x)

theorem finish_canonical_to_s (x : FinishE)
    (hx : AspisR1CurrentWide.Proof.CanonicalFinish x) :
    Canonical (finishToS x) := by
  change AspisR1CurrentWide.Proof.CanonicalWide
    (toE (fromE (AspisR1CurrentWide.Proof.ofFinishE x)))
  rw [to_from]
  exact hx

def decodeField (bytes : Slice Std.U8) (i : Std.Usize) : Result S := do
  let x ← AspisR1CurrentWide.Proof.finishField bytes i
  ok (finishToS x)

theorem decodeField_success_canonical (bytes : Slice Std.U8) (i : Std.Usize)
    (x : S) (h : decodeField bytes i = .ok x) : Canonical x := by
  unfold decodeField at h
  cases hf : AspisR1CurrentWide.Proof.finishField bytes i with
  | fail e => simp only [hf, bind_tc_fail] at h; cases h
  | div => simp only [hf, bind_tc_div] at h; cases h
  | ok y =>
    simp only [hf, bind_tc_ok] at h
    have he : finishToS y = x := Result.ok.inj h
    rw [← he]
    exact finish_canonical_to_s y
      (AspisR1CurrentWide.Proof.finishField_success_canonical bytes i y hf)

def add (x y : S) : Result S := do
  let z ← AspisR1CurrentWide.field.wide_exact.WideExact.add (toE x) (toE y)
  ok (fromE z)

theorem add_total_exact (x y : S) (hx : Canonical x) (hy : Canonical y) :
    ∃ z, add x y = .ok z ∧ Canonical z ∧ decode z = decode x + decode y := by
  obtain ⟨z, hz, hc, he⟩ :=
    AspisR1CurrentWide.Proof.wide_add_total_exact (toE x) (toE y) hx hy
  refine ⟨fromE z, ?_, ?_, ?_⟩
  · simp only [add, hz, bind_tc_ok]
  · simpa only [Canonical, to_from] using hc
  · simpa only [decode, to_from] using he

def mul (x y : S) : Result S := do
  let z ← AspisR1CurrentWide.field.wide_exact.WideExact.mul (toE x) (toE y)
  ok (fromE z)

theorem mul_total_exact (x y : S) (hx : Canonical x) (hy : Canonical y) :
    ∃ z, mul x y = .ok z ∧ Canonical z ∧ decode z = decode x * decode y := by
  obtain ⟨z, hz, hc, he⟩ :=
    AspisR1CurrentWide.Proof.wide_mul_total_exact (toE x) (toE y) hx hy
  refine ⟨fromE z, ?_, ?_, ?_⟩
  · simp only [mul, hz, bind_tc_ok]
  · simpa only [Canonical, to_from] using hc
  · simpa only [decode, to_from] using he

def actualOperations : Operations := ⟨decodeField, add, mul⟩

end ActualFieldComplete
end AspisR1GroupedPairActualFieldOpsV3

#print axioms AspisR1GroupedPairActualFieldOpsV3.ActualFieldComplete.decodeField_success_canonical
#print axioms AspisR1GroupedPairActualFieldOpsV3.ActualFieldComplete.add_total_exact
#print axioms AspisR1GroupedPairActualFieldOpsV3.ActualFieldComplete.mul_total_exact
