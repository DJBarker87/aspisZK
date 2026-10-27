from step import check,append
m='R1Z/PV_OptB_ProjectionBoundary';ns='R1Z.PV_OptB_ProjectionBoundary'
check(m)
append(m,ns,'full_state_differs','''theorem full_state_differs : (Result.ok false : Result Bool) ≠ Result.ok true := by
  intro same
  cases same
''')
append(m,ns,'observation_factor_sufficient','''theorem observation_factor_sufficient {S T E : Type}
    (project : S → T) (observe : S → E) (decode : T → E)
    (factor : ∀ s, observe s = decode (project s)) (s t : S)
    (same : project s = project t) : observe s = observe t := by
  rw [factor s,factor t,same]
''')
