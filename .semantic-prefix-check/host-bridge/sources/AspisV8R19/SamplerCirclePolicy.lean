import AspisV8R19.SamplerFieldDecode

/-! Exact-tower source-shaped circle map and bounded wrapper. The singular
check precedes the CM31 check, as in circle.rs. Inversion is mathematical;
universal Rust try_inv refinement is not asserted. -/
set_option autoImplicit false
namespace AspisV8R19.SamplerCirclePolicy
open AspisV8R15.ExactTowerBase AspisV8R15.ExactTowerChord AspisV8R15.CircleChord
open DuplexFrames SourceDuplexStep MemoizedProgramLaw BoundedSamplerWrapper
open SamplerWrapperPolicies SamplerFieldDecode
noncomputable section

def imaginaryUnit : QM31Exact := ⟨⟨0,1⟩,0⟩

theorem imaginary_square : imaginaryUnit^2 = -1 := by
  ext <;> simp [imaginaryUnit,pow_two] <;> rfl

theorem outside_has_denominator (t : QM31Exact) (ht : t.im ≠ 0) : 1+t^2 ≠ 0 := by
  intro h
  have he : t^2 = imaginaryUnit^2 := by rw [imaginary_square]; linear_combination h
  rcases (sq_eq_sq_iff_eq_or_eq_neg).mp he with h | h
  · subst t; exact ht rfl
  · subst t; exact ht rfl

inductive MapError where
  | singular
  | subfield
  deriving DecidableEq

def point (t : QM31Exact) : QM31Exact × QM31Exact := (px t,py t)
def pureMap (t : QM31Exact) : Except MapError (QM31Exact × QM31Exact) := by
  classical
  exact if 1+t^2 = 0 then .error .singular
    else if t.im = 0 then .error .subfield else .ok (point t)

theorem singular_first (t : QM31Exact) (h : 1+t^2 = 0) :
    pureMap t = .error .singular := by simp [pureMap,h]

theorem outside_map (t : QM31Exact) (ht : t.im ≠ 0) :
    pureMap t = .ok (point t) := by
  simp [pureMap,ht,outside_has_denominator t ht]

theorem success_policy (t : QM31Exact) (p : QM31Exact × QM31Exact)
    (h : pureMap t = .ok p) : t.im ≠ 0 ∧ 1+t^2 ≠ 0 ∧ p = point t := by
  by_cases hd : 1+t^2 = 0
  · simp [pureMap,hd] at h
  · by_cases hi : t.im = 0
    · simp [pureMap,hd,hi] at h
    · exact ⟨hi,hd,(by simpa [pureMap,hd,hi] using h.symm)⟩

theorem point_on_circle (t : QM31Exact) (hd : 1+t^2 ≠ 0) :
    (point t).1^2 + (point t).2^2 = 1 := by
  simp only [point,px,py]
  field_simp
  ring

theorem recover_parameter (t : QM31Exact) (hd : 1+t^2 ≠ 0) :
    (point t).2 / (1+(point t).1) = t := by
  simp only [point,px,py]
  field_simp [AspisV8R15.ExactTowerChord.two_ne_zero]
  rw [show 1+t^2+(1-t^2) = (2:QM31Exact) by ring]
  field_simp [AspisV8R15.ExactTowerChord.two_ne_zero]

theorem point_injective (t u : QM31Exact) (ht : 1+t^2 ≠ 0) (hu : 1+u^2 ≠ 0)
    (h : point t = point u) : t = u := by
  rw [← recover_parameter t ht, h, recover_parameter u hu]

theorem outside_point (t : QM31Exact) (ht : t.im ≠ 0) :
    ¬ ((point t).1.im = 0 ∧ (point t).2.im = 0) := by
  rintro ⟨hx,hy⟩
  have hm := cm31Subfield.div_mem ((mem_cm31_iff _).mpr hy)
    (cm31Subfield.add_mem cm31Subfield.one_mem ((mem_cm31_iff _).mpr hx))
  rw [recover_parameter t (outside_has_denominator t ht)] at hm
  exact ht ((mem_cm31_iff t).mp hm)

def accept (xs : List Nat) : Option (QM31Exact × QM31Exact) :=
  (pureMap (decode xs)).toOption
def circleProgram (s : State) :=
  program accept Error.challengeExhausted Error.parameterExhausted 3 s
def circleRun (H : Bytes → State) (s : State) :=
  run accept Error.challengeExhausted Error.parameterExhausted H 3 s

theorem circle_exact (H : Bytes → State) (s : State) :
    eval H (circleProgram s) = circleRun H s := exact_run _ _ _ H 3 s

theorem circle_law (s : State) :
    SamplerOracleLaws.CorrectLaw (circleProgram s) (fun H => circleRun H s) :=
  oracle_law _ _ _ 3 s

theorem accept_policy (xs : List Nat) (p : QM31Exact × QM31Exact)
    (h : accept xs = some p) :
    (decode xs).im ≠ 0 ∧ 1+(decode xs)^2 ≠ 0 ∧ p = point (decode xs) := by
  unfold accept at h
  cases hm : pureMap (decode xs) with
  | error e => simp [hm,Except.toOption] at h
  | ok q =>
      have he : q = p := by simpa [hm,Except.toOption] using h
      subst q
      exact success_policy _ p hm

theorem circle_result (H : Bytes → State) (s : State) (p : QM31Exact × QM31Exact)
    (h : (circleRun H s).2.1 = .ok p) :
    ∃ xs, xs.length = 4 ∧ (∀ a ∈ xs, a < 2147483647) ∧
      (decode xs).im ≠ 0 ∧ p = point (decode xs) ∧ p.1^2+p.2^2=1 := by
  obtain ⟨xs,hlen,hcan,ha⟩ := successful_image _ _ _ H 3 s p h
  obtain ⟨hout,hd,hp⟩ := accept_policy xs p ha
  exact ⟨xs,hlen,hcan,hout,hp,hp ▸ point_on_circle (decode xs) hd⟩

#print axioms imaginary_square
#print axioms outside_has_denominator
#print axioms singular_first
#print axioms outside_map
#print axioms success_policy
#print axioms point_on_circle
#print axioms recover_parameter
#print axioms point_injective
#print axioms outside_point
#print axioms circle_exact
#print axioms circle_law
#print axioms accept_policy
#print axioms circle_result
end
end AspisV8R19.SamplerCirclePolicy
