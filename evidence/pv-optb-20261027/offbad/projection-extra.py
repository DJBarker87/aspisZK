from step import append
m='R1Z/PV_OptB_ProjectionBoundary';ns='R1Z.PV_OptB_ProjectionBoundary'
append(m,ns,'mapR_compose','''theorem mapR_compose {S T E : Type} (project : S → T) (decode : T → E) (r : Result S) :
    mapR decode (mapR project r) = mapR (fun s => decode (project s)) r := by
  cases r <;> rfl
''')
append(m,ns,'projected_observation_sufficient','''theorem projected_observation_sufficient {S T E : Type}
    (project : S → T) (observe : S → E) (decode : T → E)
    (factor : ∀ s, observe s = decode (project s)) (left right : Result S)
    (same : mapR project left = mapR project right) : mapR observe left = mapR observe right := by
  have factor_eq : observe = fun s => decode (project s) := funext factor
  rw [factor_eq, ← mapR_compose project decode left, ← mapR_compose project decode right, same]
''')
