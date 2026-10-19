import AspisR1RhoReference.Funs
import CuSavingsRhoInitRow

/-! Compare the actual old coefficient RHS with the complete checked new push.
The scalar-tower multiplication bodies are freshly emitted; the unchanged
M31 multiplication and QM31 addition are the original checked functions. -/
set_option autoImplicit false
namespace AspisR1.CuSavingsRhoReference
open Aeneas Aeneas.Std Result AspisR1CuRho
open CuSavingsRhoValue CuSavingsRhoPush CuSavingsRhoPushStep CuSavingsRhoState
open CuSavingsRhoInitRow CuSavingsResidues AspisV8R17.RawReducer
abbrev Current := AspisR1Qm31ArithmeticProbe.field.QM31

def toCurrent (x : field.QM31) : Current :=
  {c0 := {a := x.c0.a,b := x.c0.b},c1 := {a := x.c1.a,b := x.c1.b}}
def fromCurrent (x : Current) : field.QM31 :=
  {c0 := {a := x.c0.a,b := x.c0.b},c1 := {a := x.c1.a,b := x.c1.b}}

theorem toCanonical (x : field.QM31) (h : Canonical x) :
    ExtractedCurrentTowerAdd.CanonicalQM (toCurrent x) :=
  ⟨⟨h 0,h 1⟩,⟨h 2,h 3⟩⟩

theorem word_ext (x y : field.QM31)
    (h : ∀ j : Fin 4,(wordAt (powerLimbs x) j).val = (wordAt (powerLimbs y) j).val) :
    x = y := by
  have ha := UScalar.eq_of_val_eq (h 0)
  have hb := UScalar.eq_of_val_eq (h 1)
  have hc := UScalar.eq_of_val_eq (h 2)
  have hd := UScalar.eq_of_val_eq (h 3)
  change x.c0.a = y.c0.a at ha
  change x.c0.b = y.c0.b at hb
  change x.c1.a = y.c1.a at hc
  change x.c1.b = y.c1.b at hd
  exact congrArg₂ field.QM31.mk (congrArg₂ field.CM31.mk ha hb)
    (congrArg₂ field.CM31.mk hc hd)

theorem canonical_words (row : Raw4) (j : Fin 4) :
    (wordAt (powerLimbs (canonicalValue row)) j).val = (wordAt row j).val % P := by
  fin_cases j <;> rfl

theorem canonical_bound (row : Raw4) : Canonical (canonicalValue row) := by
  intro j
  rw [canonical_words]
  exact Nat.mod_lt _ (by decide)

theorem mul_values (x : Current) (basis : U32) :
    ∃ out : Current,
      AspisR1RhoReference.field.QM31.mul_m31 x basis = .ok out ∧
      ExtractedCurrentTowerAdd.CanonicalQM out ∧
      ExtractedCurrentTowerAdd.wordsQM out =
        (((x.c0.a.val*basis.val)%P,(x.c0.b.val*basis.val)%P),
         ((x.c1.a.val*basis.val)%P,(x.c1.b.val*basis.val)%P)) := by
  obtain ⟨a,ha,hav,hac⟩ := ExtractedCurrentReducer.current_mul_mod x.c0.a basis
  obtain ⟨b,hb,hbv,hbc⟩ := ExtractedCurrentReducer.current_mul_mod x.c0.b basis
  obtain ⟨c,hc,hcv,hcc⟩ := ExtractedCurrentReducer.current_mul_mod x.c1.a basis
  obtain ⟨d,hd,hdv,hdc⟩ := ExtractedCurrentReducer.current_mul_mod x.c1.b basis
  refine ⟨⟨⟨a,b⟩,⟨c,d⟩⟩,?_,⟨⟨hac,hbc⟩,⟨hcc,hdc⟩⟩,?_⟩
  · simp only [AspisR1RhoReference.field.QM31.mul_m31,
      AspisR1RhoReference.field.CM31.mul_m31,AspisR1RhoReference.field.M31.mul,
      ha,hb,hc,hd,bind_tc_ok]
  · exact Prod.ext (Prod.ext hav hbv) (Prod.ext hcv hdv)

def referenceStep (weight power : field.QM31) (basis : U32) : Result field.QM31 := do
  let out ← AspisR1RhoReference.step (toCurrent weight) (toCurrent power) basis
  .ok (fromCurrent out)

theorem reference_values (weight power : field.QM31) (basis : U32)
    (hw : Canonical weight) :
    ∃ out : field.QM31,referenceStep weight power basis = .ok out ∧ Canonical out ∧
      ∀ j : Fin 4,(wordAt (powerLimbs out) j).val =
        ((wordAt (powerLimbs weight) j).val +
          (wordAt (powerLimbs power) j).val*basis.val)%P := by
  obtain ⟨product,hm,hc,hv⟩ := mul_values (toCurrent power) basis
  obtain ⟨out,ha,hoc,hov⟩ := ExtractedCurrentTowerAdd.current_qm_add_mod
    (toCurrent weight) product (toCanonical weight hw) hc
  refine ⟨fromCurrent out,?_,?_,?_⟩
  · simp only [referenceStep,AspisR1RhoReference.step,hm,
      AspisR1RhoReference.field.QM31.add,ha,bind_tc_ok]
  · intro j
    fin_cases j <;> first | exact hoc.1.1 | exact hoc.1.2 | exact hoc.2.1 | exact hoc.2.2
  · intro j
    fin_cases j
    · change out.c0.a.val = (weight.c0.a.val+power.c0.a.val*basis.val)%P
      have hp := congrArg (fun z : (Nat×Nat)×(Nat×Nat) => z.1.1) hv
      have ho := congrArg (fun z : (Nat×Nat)×(Nat×Nat) => z.1.1) hov
      change product.c0.a.val = (power.c0.a.val*basis.val)%P at hp
      change out.c0.a.val = (weight.c0.a.val+product.c0.a.val)%P at ho
      rw [ho,hp]
      simp only [Nat.add_mod,Nat.mod_mod]
    · change out.c0.b.val = (weight.c0.b.val+power.c0.b.val*basis.val)%P
      have hp := congrArg (fun z : (Nat×Nat)×(Nat×Nat) => z.1.2) hv
      have ho := congrArg (fun z : (Nat×Nat)×(Nat×Nat) => z.1.2) hov
      change product.c0.b.val = (power.c0.b.val*basis.val)%P at hp
      change out.c0.b.val = (weight.c0.b.val+product.c0.b.val)%P at ho
      rw [ho,hp]
      simp only [Nat.add_mod,Nat.mod_mod]
    · change out.c1.a.val = (weight.c1.a.val+power.c1.a.val*basis.val)%P
      have hp := congrArg (fun z : (Nat×Nat)×(Nat×Nat) => z.2.1) hv
      have ho := congrArg (fun z : (Nat×Nat)×(Nat×Nat) => z.2.1) hov
      change product.c1.a.val = (power.c1.a.val*basis.val)%P at hp
      change out.c1.a.val = (weight.c1.a.val+product.c1.a.val)%P at ho
      rw [ho,hp]
      simp only [Nat.add_mod,Nat.mod_mod]
    · change out.c1.b.val = (weight.c1.b.val+power.c1.b.val*basis.val)%P
      have hp := congrArg (fun z : (Nat×Nat)×(Nat×Nat) => z.2.2) hv
      have ho := congrArg (fun z : (Nat×Nat)×(Nat×Nat) => z.2.2) hov
      change product.c1.b.val = (power.c1.b.val*basis.val)%P at hp
      change out.c1.b.val = (weight.c1.b.val+product.c1.b.val)%P at ho
      rw [ho,hp]
      simp only [Nat.add_mod,Nat.mod_mod]

theorem push_reference (self : verifier.BatchedWeights) (index : Usize)
    (power : field.QM31) (basis : U32) (hi : index.val < self.raw.val.length)
    (hr : ∀ j : Fin 4,RhoBound (wordAt (self.raw.val[index.val]'hi) j).val self.terms.val)
    (hp : Canonical power) (hb : basis.val < P) :
    ∃ row : Raw4,
      verifier.BatchedWeights.push self index power basis = .ok (replaceRow self index row) ∧
      referenceStep (canonicalValue (self.raw.val[index.val]'hi)) power basis = .ok (canonicalValue row) ∧
      ∀ j : Fin 4,RhoBound (wordAt row j).val (self.terms.val+1) := by
  obtain ⟨row,hrun,hvalues⟩ := CuSavingsRhoPush.source_success self index power basis hi hr hp hb
  obtain ⟨out,href,_,hout⟩ := reference_values
    (canonicalValue (self.raw.val[index.val]'hi)) power basis (canonical_bound _)
  have heq : out = canonicalValue row := by
    apply word_ext
    intro j
    rw [hout j,canonical_words,canonical_words,(hvalues j).2]
    rw [Nat.add_mod,Nat.mod_mod,← Nat.add_mod]
  exact ⟨row,hrun,heq ▸ href,fun j => (hvalues j).1⟩

#print axioms mul_values
#print axioms reference_values
#print axioms push_reference
end AspisR1.CuSavingsRhoReference
