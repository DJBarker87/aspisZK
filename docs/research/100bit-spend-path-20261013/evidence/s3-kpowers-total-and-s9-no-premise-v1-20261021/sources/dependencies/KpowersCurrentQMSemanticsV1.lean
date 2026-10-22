import KpowersP6PowerSemanticsV1
import CurrentWideQMField

open Aeneas Aeneas.Std Result
set_option autoImplicit false

namespace AspisR1S9HelperP6PowerSemanticsV1

open AspisR1S9HelperP6

abbrev GQM := AspisR1S9HelperP6.field.QM31
abbrev CQM := AspisR1CurrentWide.field.QM31
abbrev ExactQM := AspisR1CurrentWide.Proof.ExactQM

def helperToCurrentQM (x : GQM) : CQM :=
  ⟨⟨x.c0.a, x.c0.b⟩, ⟨x.c1.a, x.c1.b⟩⟩

def currentToHelperQM (x : CQM) : GQM :=
  ⟨⟨x.c0.a, x.c0.b⟩, ⟨x.c1.a, x.c1.b⟩⟩

def currentQMOne : CQM :=
  ⟨⟨1#u32, 0#u32⟩, ⟨0#u32, 0#u32⟩⟩

@[simp] theorem currentToHelper_helperToCurrent (x : GQM) :
    currentToHelperQM (helperToCurrentQM x) = x := by cases x; rfl

@[simp] theorem helperToCurrent_currentToHelper (x : CQM) :
    helperToCurrentQM (currentToHelperQM x) = x := by cases x; rfl

@[reducible] def currentQMOps : FieldOps where
  qmMul x y := do
    let z ← AspisR1CurrentWide.field.QM31.mul
      (helperToCurrentQM x) (helperToCurrentQM y)
    ok (currentToHelperQM z)
  qmSquare _ := .div
  wideAdd _ _ := .div
  wideMul _ _ := .div
  wideMulM31 _ _ := .div
  wideMulQM31 _ _ := .div
  iterFold _ _ _ _ _ := .div

instance currentFieldOps : FieldOps := currentQMOps

def currentQMSemantics : QMSemantics ExactQM := {
    canonical := fun x => AspisR1CurrentWide.Proof.CanonicalQM (helperToCurrentQM x)
    decode := fun x => AspisR1CurrentWide.Proof.decodeQM (helperToCurrentQM x)
    one_canonical := by
      unfold helperToCurrentQM AspisR1S9HelperP6.field.QM31.ONE
      change AspisR1CurrentWide.Proof.CanonicalQM currentQMOne
      norm_num [AspisR1CurrentWide.Proof.CanonicalQM,
        AspisR1CurrentWide.Proof.toQM, AspisR1CurrentWide.Proof.toCM,
        AspisR1.ExtractedCurrentQM31Exact.CurrentCanonicalQM,
        AspisR1.ExtractedCurrentQM31Tower.CurrentCanonicalQM,
        AspisR1.ExtractedCurrentTowerAdd.CanonicalQM,
        AspisR1.ExtractedCurrentTowerAdd.CanonicalCM,
        AspisR1.ExtractedCurrentTowerAdd.P,
        AspisR1.ExtractedCurrentM31AddSub.P,
        currentQMOne]
    decode_one := by
      unfold helperToCurrentQM AspisR1S9HelperP6.field.QM31.ONE
      change AspisR1CurrentWide.Proof.decodeQM currentQMOne = 1
      norm_num [AspisR1CurrentWide.Proof.decodeQM,
        AspisR1CurrentWide.Proof.toQM, AspisR1CurrentWide.Proof.toCM,
        AspisR1.ExtractedCurrentQM31Exact.decode,
        AspisR1.ExtractedCurrentQM31Exact.CurrentQM,
        AspisR1.ExtractedCurrentQM31Tower.decode,
        AspisR1.ExtractedCurrentQM31Mul.wordsQM,
        currentQMOne] <;> rfl
    mul_success := by
      intro x y z hx hy h
      change (do
        let out ← AspisR1CurrentWide.field.QM31.mul
          (helperToCurrentQM x) (helperToCurrentQM y)
        ok (currentToHelperQM out)) = .ok z at h
      cases hm : AspisR1CurrentWide.field.QM31.mul
        (helperToCurrentQM x) (helperToCurrentQM y) with
      | fail e => simp [hm] at h
      | div => simp [hm] at h
      | ok out =>
          have hout : currentToHelperQM out = z := by
            simpa [hm, bind_tc_ok] using h
          have hcurrent : AspisR1CurrentWide.field.QM31.mul
              (helperToCurrentQM x) (helperToCurrentQM y) =
              .ok (helperToCurrentQM z) := by
            rw [hm]
            apply congrArg Result.ok
            calc
              out = helperToCurrentQM (currentToHelperQM out) := by simp
              _ = helperToCurrentQM z := congrArg helperToCurrentQM hout
          have hx' : AspisR1CurrentWide.Proof.CanonicalQM (helperToCurrentQM x) := hx
          have hy' : AspisR1CurrentWide.Proof.CanonicalQM (helperToCurrentQM y) := hy
          obtain ⟨hz, hdecode⟩ :=
            AspisR1CurrentWide.Proof.qm_mul_success
              (helperToCurrentQM x) (helperToCurrentQM y)
              (helperToCurrentQM z) hx' hy' hcurrent
          constructor
          · exact hz
          · exact hdecode
  }

theorem currentQMSemantics_mul_installs_operation (x y : GQM) :
    @FieldOps.qmMul currentQMOps x y =
      (do
        let z ← AspisR1CurrentWide.field.QM31.mul
          (helperToCurrentQM x) (helperToCurrentQM y)
        ok (currentToHelperQM z)) := rfl

#print axioms currentQMSemantics
#print axioms currentQMSemantics_mul_installs_operation

end AspisR1S9HelperP6PowerSemanticsV1
