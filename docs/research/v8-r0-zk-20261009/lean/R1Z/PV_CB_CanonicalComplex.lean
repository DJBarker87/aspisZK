import R1Z.PV_CB_CanonicalTower
import R1Z.ProverCommitNativeC49
set_option autoImplicit false
namespace R1Z.PV_CB_CanonicalComplex
open Aeneas Aeneas.Std Result
abbrev C := ProverRwFull.aspis_core.field.CM31
abbrev OldC := ProverCommitPrimitive47.Old.C

def old (x : C) : OldC := ⟨x.a,x.b⟩
def current (x : OldC) : C := ⟨x.a,x.b⟩
def Valid (x : C) : Prop := ProverCommitNativeC49.Canonical (old x)

theorem source (x : C) : ProverRwDictionaryTower.toC x =
    ProverCommitNativeC49.source (old x) := rfl

theorem valid_current (x : OldC) (valid : ProverCommitNativeC49.Canonical x) :
    Valid (current x) := valid

theorem add (a b : C) (ha : Valid a) (hb : Valid b) :
    ∃ value, PV_CB_CurrentComplex.S.add a b = ok value ∧ Valid value := by
  obtain ⟨value,hvalue,hcanonical,_⟩ := ProverCommitNativeC49.add (old a) (old b) ha hb
  refine ⟨current value,?_,valid_current value hcanonical⟩
  rw [PV_CB_CurrentComplex.add,source,source,hvalue]
  rfl

theorem sub (a b : C) (ha : Valid a) (hb : Valid b) :
    ∃ value, PV_CB_CurrentComplex.S.sub a b = ok value ∧ Valid value := by
  obtain ⟨value,hvalue,hcanonical,_⟩ := ProverCommitNativeC49.sub (old a) (old b) ha hb
  refine ⟨current value,?_,valid_current value hcanonical⟩
  rw [PV_CB_CurrentComplex.sub,source,source,hvalue]
  rfl

theorem mul (a b : C) (ha : Valid a) (hb : Valid b) :
    ∃ value, PV_CB_CurrentComplex.S.mul a b = ok value ∧ Valid value := by
  obtain ⟨value,hvalue,hcanonical,_⟩ := ProverCommitNativeC49.mul (old a) (old b) ha hb
  refine ⟨current value,?_,valid_current value hcanonical⟩
  rw [PV_CB_CurrentComplex.mul,source,source,hvalue]
  rfl

theorem r (a : C) (ha : Valid a) :
    ∃ value, PV_CB_CurrentQuartic.S.r a = ok value ∧ Valid value := by
  obtain ⟨value,hvalue,hcanonical,_⟩ := ProverCommitNativeC49.mul_r (old a) ha
  refine ⟨current value,?_,valid_current value hcanonical⟩
  rw [PV_CB_CurrentQuartic.r,source,hvalue]
  rfl
#print axioms source
#print axioms valid_current
#print axioms add
#print axioms sub
#print axioms mul
#print axioms r
end R1Z.PV_CB_CanonicalComplex
