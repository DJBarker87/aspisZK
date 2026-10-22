import CurrentWideProduct
import CurrentWideMulM31V13
import FinishCandidateEquations
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1CurrentWide.Proof
abbrev FinishE := AspisR1FinishRelationCurrent.aspis_core.field.WideExact
abbrev FinishQM := AspisR1FinishRelationCurrent.aspis_core.field.QM31
abbrev FinishCM := AspisR1FinishRelationCurrent.aspis_core.field.CM31

def ofFinishCM (x : FinishCM) : field.CM31 := ⟨x.a,x.b⟩
def ofFinishQM (x : FinishQM) : field.QM31 := ⟨ofFinishCM x.c0,ofFinishCM x.c1⟩
def ofFinishE (x : FinishE) : E := ⟨ofFinishQM x.c0,ofFinishQM x.c1⟩
def toFinishCM (x : field.CM31) : FinishCM := ⟨x.a,x.b⟩
def toFinishQM (x : field.QM31) : FinishQM := ⟨toFinishCM x.c0,toFinishCM x.c1⟩
def toFinishE (x : E) : FinishE := ⟨toFinishQM x.c0,toFinishQM x.c1⟩
theorem of_to_finish (x : E) : ofFinishE (toFinishE x)=x := rfl
theorem to_of_finish (x : FinishE) : toFinishE (ofFinishE x)=x := rfl

def CanonicalFinish (x : FinishE) : Prop := CanonicalWide (ofFinishE x)
def decodeFinish (x : FinishE) : AspisWideTower.WideExact := decodeWide (ofFinishE x)
def finishAdd (x y : FinishE) : Result FinishE := do
  let z ← field.wide_exact.WideExact.add (ofFinishE x) (ofFinishE y)
  ok (toFinishE z)
def finishScale (x : FinishE) (s : U32) : Result FinishE := do
  let z ← field.wide_exact.WideExact.mul_m31 (ofFinishE x) s
  ok (toFinishE z)
def finishArithmetic {W D : Type} (ops : AspisR1FinishRelationCurrent.FinishOps W D) :
    AspisR1FinishRelationCurrent.FinishOps W D :=
  {ops with add:=finishAdd, mulM31:=finishScale, quarter:=.ok 536870912#u32}

theorem finish_add_success (x y z : FinishE) (hx : CanonicalFinish x) (hy : CanonicalFinish y)
    (h : finishAdd x y = .ok z) :
    CanonicalFinish z ∧ decodeFinish z=decodeFinish x+decodeFinish y := by
  unfold finishAdd at h
  cases ho : field.wide_exact.WideExact.add (ofFinishE x) (ofFinishE y) with
  | fail e => simp only [ho,bind_tc_fail] at h; cases h
  | div => simp only [ho,bind_tc_div] at h; cases h
  | ok out =>
    simp only [ho,bind_tc_ok] at h
    have hz : toFinishE out=z := Result.ok.inj h
    have hr := wide_add_success (ofFinishE x) (ofFinishE y) out hx hy ho
    change CanonicalWide (ofFinishE z) ∧ decodeWide (ofFinishE z)=decodeWide (ofFinishE x)+decodeWide (ofFinishE y)
    rw [←hz,of_to_finish]
    exact hr

theorem finish_scale_success (x z : FinishE) (s : U32) (hx : CanonicalFinish x)
    (h : finishScale x s = .ok z) :
    CanonicalFinish z ∧ decodeFinish z=decodeFinish x *
      algebraMap (ZMod AspisV8R15.ExactTowerBase.P) AspisWideTower.WideExact
        (R17CurrentM31Semantics.decode s) := by
  unfold finishScale at h
  cases ho : field.wide_exact.WideExact.mul_m31 (ofFinishE x) s with
  | fail e => simp only [ho,bind_tc_fail] at h; cases h
  | div => simp only [ho,bind_tc_div] at h; cases h
  | ok out =>
    simp only [ho,bind_tc_ok] at h
    have hz : toFinishE out=z := Result.ok.inj h
    have hr := wide_mul_m31_success_algebraMap (ofFinishE x) out s hx ho
    change CanonicalWide (ofFinishE z) ∧ decodeWide (ofFinishE z)=decodeWide (ofFinishE x)*_
    rw [←hz,of_to_finish]
    exact hr

theorem current_round_equation {W D : Type} (ops : AspisR1FinishRelationCurrent.FinishOps W D)
    (poly : Slice U8) (alpha claim out : FinishE)
    (hc : CanonicalFinish claim)
    (h0 : ∀ x, ops.field poly 0#usize = .ok x → CanonicalFinish x)
    (h4 : ∀ x, ops.field poly 4#usize = .ok x → CanonicalFinish x)
    (h : AspisR1FinishRelationCurrent.FinishCandidateEquations.RoundEquation
      (finishArithmetic ops) poly alpha claim out) :
    ∃ x0 x4, ops.field poly 0#usize=.ok x0 ∧ ops.field poly 4#usize=.ok x4 ∧
      decodeFinish x0+decodeFinish x4=decodeFinish claim * (536870912 : AspisWideTower.WideExact) := by
  rcases h with ⟨x0,x4,lhs,q,rhs,hx0,hx4,ha,hq,hm,he,_⟩
  have hq' : 536870912#u32=q := Result.ok.inj hq
  subst q
  have Hlhs := finish_add_success x0 x4 lhs (h0 x0 hx0) (h4 x4 hx4) ha
  have Hrhs := finish_scale_success claim rhs 536870912#u32 hc hm
  refine ⟨x0,x4,hx0,hx4,?_⟩
  calc
    decodeFinish x0+decodeFinish x4=decodeFinish lhs := Hlhs.2.symm
    _ = decodeFinish rhs := congrArg decodeFinish he
    _ = decodeFinish claim * (536870912 : AspisWideTower.WideExact) := by
      rw [Hrhs.2]
      congr 1

#print axioms of_to_finish
#print axioms to_of_finish
#print axioms finish_add_success
#print axioms finish_scale_success
#print axioms current_round_equation
end AspisR1CurrentWide.Proof
