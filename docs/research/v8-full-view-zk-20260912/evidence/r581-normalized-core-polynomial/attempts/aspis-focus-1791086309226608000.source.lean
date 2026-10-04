import AspisV8R19.R574SparseGCorePolynomial
import AspisV8R17.MinorDegree

set_option autoImplicit false
namespace AspisV8R19.R581NormalizedCorePolynomial

open MvPolynomial AspisV8R19.R574SparseGCorePolynomial

variable {F : Type*} [Field F] [NeZero (2 : F)]

abbrev Poly (F : Type*) [CommSemiring F] := MvPolynomial (Fin 3) F

def circleAssignment (alpha u v : F) : Fin 3 → F :=
  fun i => if i.val = 0 then alpha else if i.val = 1 then u else v

def normalizedChordAssignment (u v : F) : Fin 4 → F :=
  fun i => if i.val = 0 then 1 else if i.val = 1 then 1 + u*v
    else if i.val = 2 then u*v - 1 else -(u+v)

noncomputable def substitution : Fin 4 → Poly F := fun i =>
  if i.val = 0 then X (0 : Fin 3)
  else if i.val = 1 then 1 + X (1 : Fin 3) * X (2 : Fin 3)
  else if i.val = 2 then X (1 : Fin 3) * X (2 : Fin 3) - 1
  else -(X (1 : Fin 3) + X (2 : Fin 3))

noncomputable def substitute (p : MvPolynomial (Fin 4) F) : Poly F :=
  eval₂ (C : F →+* Poly F) substitution p

noncomputable def normalizedPolynomialMatrix (half : F) : Matrix (Fin 271) (Fin 271) (Poly F) :=
  fun i j => substitute (corePolynomialMatrix half i j)

noncomputable def normalizedComponent (half : F) (u v w : F)
    (q0 q1 q2 q3 : Nat → F) (i : Fin 271) : Poly F :=
  C (sourceBasisValue half q0 u v w i) - X (0 : Fin 3) * C (sourceBasisValue half q1 u v w i) -
    X (0 : Fin 3)^2 * C (sourceBasisValue half q2 u v w i) -
    X (0 : Fin 3)^3 * C (sourceBasisValue half q3 u v w i)

noncomputable def normalizedEntry (half : F) (i j : Fin 271) : Poly F :=
  (1 + X (1 : Fin 3) * X (2 : Fin 3)) *
      normalizedComponent half 1 0 0 (nz (basis j)) (ch 1 (basis j))
        (ch 2 (basis j)) (ch 3 (basis j)) i +
  (X (1 : Fin 3) * X (2 : Fin 3) - 1) *
      normalizedComponent half 0 1 0 (nz (basis j)) (ch 1 (basis j))
        (ch 2 (basis j)) (ch 3 (basis j)) i +
  (-(X (1 : Fin 3) + X (2 : Fin 3))) *
      normalizedComponent half 0 0 1 (nz (basis j)) (ch 1 (basis j))
        (ch 2 (basis j)) (ch 3 (basis j)) i

omit [NeZero (2 : F)] in
theorem substitute_component (half : F) (u v w : F) (q0 q1 q2 q3 : Nat → F)
    (i : Fin 271) :
    substitute (componentPolynomial half u v w q0 q1 q2 q3 i) =
      normalizedComponent half u v w q0 q1 q2 q3 i := by
  change (eval₂Hom (C : F →+* Poly F) substitution)
      (componentPolynomial half u v w q0 q1 q2 q3 i) = _
  simp only [componentPolynomial, normalizedComponent, map_sub, map_mul, map_pow,
    MvPolynomial.eval₂Hom_C, MvPolynomial.eval₂Hom_X']
  simp [substitution]

theorem normalizedEntry_eq_substitute (half : F) (i j : Fin 271) :
    normalizedEntry half i j = substitute (coreEntryPolynomial half i j) := by
  unfold normalizedEntry coreEntryPolynomial
  change _ = (eval₂Hom (C : F →+* Poly F) substitution) _
  simp only [map_add, map_mul, MvPolynomial.eval₂Hom_X']
  simp [substitution]
  rw [← substitute_component, ← substitute_component, ← substitute_component]
  rfl

theorem normalizedPolynomialMatrix_eq_entry (half : F) :
    normalizedPolynomialMatrix half = normalizedEntry half := by
  funext i j
  exact (normalizedEntry_eq_substitute half i j).symm

omit [NeZero (2 : F)] in
theorem normalizedComponent_degree (half : F) (u v w : F)
    (q0 q1 q2 q3 : Nat → F) (i : Fin 271) :
    (normalizedComponent half u v w q0 q1 q2 q3 i).totalDegree ≤ 3 := by
  unfold normalizedComponent
  have hc (x : F) : (C x : Poly F).totalDegree ≤ 0 := by simp
  have hx (n : Nat) : ((X (0:Fin 3) : Poly F)^n).totalDegree ≤ n := by
    have hpow := totalDegree_pow (X (0:Fin 3) : Poly F) n
    simpa using hpow.trans (Nat.mul_le_mul_left n
      (by simp : (X (0:Fin 3) : Poly F).totalDegree ≤ 1))
  have hm (n : Nat) (q : Nat → F) :
      ((X (0:Fin 3) : Poly F)^n * C (sourceBasisValue half q u v w i)).totalDegree ≤ n :=
    (totalDegree_mul _ _).trans (Nat.add_le_add (hx n) (hc _))
  have h0 : (C (sourceBasisValue half q0 u v w i) : Poly F).totalDegree ≤ 0 := hc _
  have h1 := hm 1 q1
  have h2 := hm 2 q2
  have h3 := hm 3 q3
  have h1' : (X (0:Fin 3) * C (sourceBasisValue half q1 u v w i)).totalDegree ≤ 1 := by
    simpa using h1
  have h2' : (X (0:Fin 3)^2 * C (sourceBasisValue half q2 u v w i)).totalDegree ≤ 2 := by
    simpa using h2
  have h3' : (X (0:Fin 3)^3 * C (sourceBasisValue half q3 u v w i)).totalDegree ≤ 3 := by
    simpa using h3
  have hab : (C (sourceBasisValue half q0 u v w i) -
      X (0:Fin 3) * C (sourceBasisValue half q1 u v w i)).totalDegree ≤ 1 :=
    (totalDegree_sub _ _).trans (max_le (h0.trans (by omega)) h1')
  have habc : ((C (sourceBasisValue half q0 u v w i) -
      X (0:Fin 3) * C (sourceBasisValue half q1 u v w i)) -
      X (0:Fin 3)^2 * C (sourceBasisValue half q2 u v w i)).totalDegree ≤ 2 :=
    (totalDegree_sub _ _).trans (max_le (hab.trans (by omega)) h2')
  exact (totalDegree_sub _ _).trans (max_le (habc.trans (by omega)) h3')

theorem normalizedEntry_degree (half : F) (i j : Fin 271) :
    (normalizedEntry half i j).totalDegree ≤ 5 := by
  unfold normalizedEntry
  have hcomp : ∀ u v w q0 q1 q2 q3,
      (normalizedComponent half u v w q0 q1 q2 q3 i).totalDegree ≤ 3 := by
    intro u v w q0 q1 q2 q3
    exact normalizedComponent_degree half u v w q0 q1 q2 q3 i
  have hx (n : Fin 3) : ((X n : Poly F)).totalDegree ≤ 1 := by simp
  have hmul (p q : Poly F) (hp : p.totalDegree ≤ 2) (hq : q.totalDegree ≤ 3) :
      (p*q).totalDegree ≤ 5 := (totalDegree_mul _ _).trans (by omega)
  have hp_uv : ((X (1:Fin 3) * X (2:Fin 3) : Poly F)).totalDegree ≤ 2 :=
    (totalDegree_mul _ _).trans (by have := hx 1; have := hx 2; omega)
  have hp_a : ((1 + X (1:Fin 3)*X (2:Fin 3) : Poly F)).totalDegree ≤ 2 :=
    (totalDegree_add _ _).trans (max_le (by simp) hp_uv)
  have hp_b : ((X (1:Fin 3)*X (2:Fin 3)-1 : Poly F)).totalDegree ≤ 2 :=
    (totalDegree_sub _ _).trans (max_le hp_uv (by simp))
  have hp_c : ((-(X (1:Fin 3)+X (2:Fin 3)) : Poly F)).totalDegree ≤ 2 := by
    rw [totalDegree_neg]
    exact (totalDegree_add _ _).trans (max_le (by simp) (by simp))
  have hA : ((1 + X (1:Fin 3)*X (2:Fin 3)) *
      normalizedComponent half 1 0 0 (nz (basis j)) (ch 1 (basis j))
        (ch 2 (basis j)) (ch 3 (basis j)) i).totalDegree ≤ 5 :=
    hmul _ _ hp_a (hcomp 1 0 0 (nz (basis j)) (ch 1 (basis j))
      (ch 2 (basis j)) (ch 3 (basis j)))
  have hB : ((X (1:Fin 3)*X (2:Fin 3)-1) *
      normalizedComponent half 0 1 0 (nz (basis j)) (ch 1 (basis j))
        (ch 2 (basis j)) (ch 3 (basis j)) i).totalDegree ≤ 5 :=
    hmul _ _ hp_b (hcomp 0 1 0 (nz (basis j)) (ch 1 (basis j))
      (ch 2 (basis j)) (ch 3 (basis j)))
  have hC : ((-(X (1:Fin 3)+X (2:Fin 3))) *
      normalizedComponent half 0 0 1 (nz (basis j)) (ch 1 (basis j))
        (ch 2 (basis j)) (ch 3 (basis j)) i).totalDegree ≤ 5 :=
    hmul _ _ hp_c (hcomp 0 0 1 (nz (basis j)) (ch 1 (basis j))
      (ch 2 (basis j)) (ch 3 (basis j)))
  exact (totalDegree_add _ _).trans
    (max_le ((totalDegree_add _ _).trans (max_le hA hB)) hC)

theorem normalizedPolynomialDet_degree (half : F) :
    (normalizedPolynomialMatrix half).det.totalDegree ≤ 1355 := by
  rw [normalizedPolynomialMatrix_eq_entry]
  simpa using AspisV8R17.minor_totalDegree (normalizedEntry half) 5
    (normalizedEntry_degree half)

theorem normalizedPolynomialMatrix_eval (half alpha u v : F) :
    (eval (circleAssignment alpha u v)).mapMatrix (normalizedPolynomialMatrix half) =
      coreMatrix half alpha (1+u*v) (u*v-1) (-(u+v)) := by
  ext i j
  change eval (circleAssignment alpha u v)
      (eval₂ (C : F →+* Poly F) substitution (coreEntryPolynomial half i j)) = _
  let ev : Poly F →+* F := eval (circleAssignment alpha u v)
  have hcomp : ev.comp (eval₂Hom (C : F →+* Poly F) substitution) =
      eval₂Hom (RingHom.id F) (fun k => ev (substitution k)) := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [ev]
    · intro k
      simp [ev]
  have h := congrArg (fun f : MvPolynomial (Fin 4) F →+* F =>
      f (coreEntryPolynomial half i j)) hcomp
  have hvalues : (fun k => ev (substitution k)) =
      coreAssignment alpha (1+u*v) (u*v-1) (-(u+v)) := by
    funext k
    fin_cases k <;> simp [ev, substitution, circleAssignment, coreAssignment] <;> try ring
  have hid : eval₂Hom (RingHom.id F)
      (coreAssignment alpha (1+u*v) (u*v-1) (-(u+v))) =
      eval (coreAssignment alpha (1+u*v) (u*v-1) (-(u+v))) := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp
    · intro k
      simp
  calc
    eval (circleAssignment alpha u v)
        (eval₂ (C : F →+* Poly F) substitution (coreEntryPolynomial half i j)) =
        eval₂Hom (RingHom.id F) (fun k => ev (substitution k))
          (coreEntryPolynomial half i j) := h
    _ = coreMatrix half alpha (1+u*v) (u*v-1) (-(u+v)) i j := by
      rw [hvalues]
      rw [hid]
      exact coreEntryPolynomial_eval half alpha (1+u*v) (u*v-1) (-(u+v)) i j

theorem normalizedPolynomialDet_eval (half alpha u v : F) :
    eval (circleAssignment alpha u v) (normalizedPolynomialMatrix half).det =
      (coreMatrix half alpha (1+u*v) (u*v-1) (-(u+v))).det := by
  rw [(eval (circleAssignment alpha u v)).map_det, normalizedPolynomialMatrix_eval]

theorem normalizedPolynomialDet_ne_zero (half : F) (hi : ∃ z : F, z*z = -1) :
    (normalizedPolynomialMatrix half).det ≠ 0 := by
  intro hzero
  obtain ⟨z, hz⟩ := hi
  have hz1 : z * (-z) = 1 := by rw [mul_neg, hz, neg_neg]
  have ha : 1 + z * (-z) = (2:F) := by rw [hz1]; ring
  have hb : z * (-z) - 1 = (0:F) := by rw [hz1]; ring
  have hc : -(z + (-z)) = (0:F) := by ring
  have he := normalizedPolynomialDet_eval half 1 z (-z)
  rw [hzero, map_zero] at he
  rw [ha, hb, hc] at he
  exact coreMatrix_witness_det_ne_zero half he.symm

end AspisV8R19.R581NormalizedCorePolynomial

#print axioms AspisV8R19.R581NormalizedCorePolynomial.substitute_component
#print axioms AspisV8R19.R581NormalizedCorePolynomial.normalizedEntry_eq_substitute
#print axioms AspisV8R19.R581NormalizedCorePolynomial.normalizedPolynomialMatrix_eval
#print axioms AspisV8R19.R581NormalizedCorePolynomial.normalizedPolynomialDet_eval
#print axioms AspisV8R19.R581NormalizedCorePolynomial.normalizedPolynomialDet_ne_zero
#print axioms AspisV8R19.R581NormalizedCorePolynomial.normalizedComponent_degree
#print axioms AspisV8R19.R581NormalizedCorePolynomial.normalizedEntry_degree
#print axioms AspisV8R19.R581NormalizedCorePolynomial.normalizedPolynomialDet_degree
