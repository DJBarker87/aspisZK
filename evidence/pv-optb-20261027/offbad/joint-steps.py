from step import check,append
m='R1Z/PV_OptB_JointTransport';ns='R1Z.PV_OptB_JointTransport'
check(m)
steps=[('overlay_none','''theorem overlay_none {Ω E V : Type} (signal : Ω → Option E) (normal : Ω → V)
    (failure : E → V) (r : Ω) (h : signal r = none) : overlay signal normal failure r = normal r := by
  simp only [overlay,h]
'''),('overlay_some','''theorem overlay_some {Ω E V : Type} (signal : Ω → Option E) (normal : Ω → V)
    (failure : E → V) (r : Ω) (e : E) (h : signal r = some e) : overlay signal normal failure r = failure e := by
  simp only [overlay,h]
'''),('overlay_bounds','''theorem overlay_bounds {Ω E : Type} (signal : Ω → Option E) (normal : Ω → ℚ)
    (failure : E → ℚ) (hn : ∀ r, 0 ≤ normal r ∧ normal r ≤ 1)
    (hf : ∀ e, 0 ≤ failure e ∧ failure e ≤ 1) (r : Ω) :
    0 ≤ overlay signal normal failure r ∧ overlay signal normal failure r ≤ 1 := by
  unfold overlay
  cases signal r with
  | none => exact hn r
  | some e => exact hf e
'''),('overlay_agreement','''theorem overlay_agreement {Ω E V : Type} (leftSignal rightSignal : Ω → Option E)
    (left right : Ω → V) (failure : E → V) (r : Ω)
    (same : leftSignal r = rightSignal r)
    (success : leftSignal r = none → left r = right r) :
    overlay leftSignal left failure r = overlay rightSignal right failure r := by
  unfold overlay
  rw [← same]
  cases hs : leftSignal r with
  | none => exact success hs
  | some e => rfl
'''),('until_bad_overlay','''theorem until_bad_overlay {Ω E : Type} [Fintype Ω]
    (leftSignal rightSignal : Ω → Option E) (left right : Ω → ℚ) (failure : E → ℚ)
    (bad : Ω → Prop)
    (hl : ∀ r, 0 ≤ left r ∧ left r ≤ 1) (hr : ∀ r, 0 ≤ right r ∧ right r ≤ 1)
    (hf : ∀ e, 0 ≤ failure e ∧ failure e ≤ 1)
    (same : ∀ r, ¬ bad r → leftSignal r = rightSignal r)
    (success : ∀ r, ¬ bad r → leftSignal r = none → left r = right r) :
    |mean (overlay leftSignal left failure) - mean (overlay rightSignal right failure)| ≤ eventMass bad := by
  exact until_bad _ _ (overlay_bounds leftSignal left failure hl hf)
    (overlay_bounds rightSignal right failure hr hf) bad
    (fun r good => overlay_agreement leftSignal rightSignal left right failure r (same r good) (success r good))
'''),('same_bound_no_new_charge','''theorem same_bound_no_new_charge {Ω E : Type} [Fintype Ω]
    (leftSignal rightSignal : Ω → Option E) (left right : Ω → ℚ) (failure : E → ℚ)
    (bad : Ω → Prop) (ε : ℚ) (mass_bound : eventMass bad ≤ ε)
    (hl : ∀ r, 0 ≤ left r ∧ left r ≤ 1) (hr : ∀ r, 0 ≤ right r ∧ right r ≤ 1)
    (hf : ∀ e, 0 ≤ failure e ∧ failure e ≤ 1)
    (same : ∀ r, ¬ bad r → leftSignal r = rightSignal r)
    (success : ∀ r, ¬ bad r → leftSignal r = none → left r = right r) :
    |mean (overlay leftSignal left failure) - mean (overlay rightSignal right failure)| ≤ ε :=
  (until_bad_overlay leftSignal rightSignal left right failure bad hl hr hf same success).trans mass_bound
'''),('observe_overlay','''theorem observe_overlay {Ω E V U : Type}
    (signal : Ω → Option E) (normal : Ω → V) (failure : E → V) (observe : V → U) :
    (fun r => observe (overlay signal normal failure r)) =
      overlay signal (fun r => observe (normal r)) (fun e => observe (failure e)) := by
  funext r
  unfold overlay
  cases signal r <;> rfl
''')]
for name,body in steps:append(m,ns,name,body)
