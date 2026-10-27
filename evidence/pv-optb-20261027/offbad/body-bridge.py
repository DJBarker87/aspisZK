from step import append
m='R1Z/PV_OptB_BodySync';ns='R1Z.PV_OptB_BodySync'
append(m,ns,'body_steps_off_bad','''theorem body_steps_off_bad {N L C W Public World Coins : Type}
    (pub : W → Public) (bad : W → World → Coins → Prop)
    (account : ProverRwEffectCallback.Account (State N L C))
    (body : W → Body (State N L C))
    (body_law : ∀ w u, pub w = pub u → ∀ os coins,
      ¬ bad w os coins → ¬ bad u os coins → ∀ secret state,
      BodyRelated Eq (body w secret state) (body u secret state)) :
    PV_OptB_OffBadJoin.Steps pub bad account body Eq := by
  intro w u same os coins hw hu i s t _ equal
  subst t
  exact attempt_related_at_same_state account (body w) (body u) i s
    (body_law w u same os coins hw hu)
''')
append(m,ns,'body_signal_off_bad','''theorem body_signal_off_bad {N L C W Public World Coins Event : Type}
    (pub : W → Public) (bad : W → World → Coins → Prop)
    (account : ProverRwEffectCallback.Account (State N L C))
    (body : W → Body (State N L C)) (initial : World → Coins → State N L C)
    (body_law : ∀ w u, pub w = pub u → ∀ os coins,
      ¬ bad w os coins → ¬ bad u os coins → ∀ secret state,
      BodyRelated Eq (body w secret state) (body u secret state))
    (decode : Result (State N L C) → Option Event) :
    PV_OptB_Factorization.IndependentOffBad pub
      (fun w os coins => decode (PV_OptB_ControlObservation.observation id
        (client account (body w) (initial os coins)))) bad :=
  PV_OptB_OffBadJoin.independent_off_bad pub bad account body initial Eq
    (body_steps_off_bad pub bad account body body_law) (fun _ _ => rfl)
    id (fun _ _ h => h) decode
''')
