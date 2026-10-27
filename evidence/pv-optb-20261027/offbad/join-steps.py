import pathlib,subprocess
p=pathlib.Path('docs/research/v8-r0-zk-20261009/lean/R1Z/PV_OptB_OffBadJoin.lean');ns='R1Z.PV_OptB_OffBadJoin'
steps=[('observations_off_bad','''theorem observations_off_bad
    (pub : W → Public) (bad : W → World → Coins → Prop)
    (account : ProverRwEffectCallback.Account (State N L C))
    (body : W → Body (State N L C))
    (R : State N L C → State N L C → Prop)
    (steps : Steps pub bad account body R) (read : State N L C → E)
    (preserved : ∀ s t, R s t → read s = read t)
    (w u : W) (same : pub w = pub u) (os : World) (coins : Coins)
    (hw : ¬ bad w os coins) (hu : ¬ bad u os coins)
    (s t : State N L C) (initial : R s t) :
    observation read (client account (body w) s) = observation read (client account (body u) t) :=
  observation_equal R read read preserved _ _
    (related_off_bad pub bad account body R steps w u same os coins hw hu s t initial)
'''),('independent_off_bad','''theorem independent_off_bad
    (pub : W → Public) (bad : W → World → Coins → Prop)
    (account : ProverRwEffectCallback.Account (State N L C))
    (body : W → Body (State N L C))
    (initial : World → Coins → State N L C)
    (R : State N L C → State N L C → Prop)
    (steps : Steps pub bad account body R)
    (initial_related : ∀ os coins, R (initial os coins) (initial os coins))
    (read : State N L C → E) (preserved : ∀ s t, R s t → read s = read t)
    (decode : Result E → Option Event) :
    PV_OptB_Factorization.IndependentOffBad pub
      (fun w os coins => decode (observation read (client account (body w) (initial os coins)))) bad := by
  intro w u same os coins hw hu
  exact congrArg decode (observations_off_bad pub bad account body R steps read preserved
    w u same os coins hw hu (initial os coins) (initial os coins) (initial_related os coins))
'''),('decoder_off_bad','''theorem decoder_off_bad
    (pub : W → Public) (bad : W → World → Coins → Prop)
    (account : ProverRwEffectCallback.Account (State N L C))
    (body : W → Body (State N L C))
    (initial : World → Coins → State N L C)
    (R : State N L C → State N L C → Prop)
    (steps : Steps pub bad account body R)
    (initial_related : ∀ os coins, R (initial os coins) (initial os coins))
    (read : State N L C → E) (preserved : ∀ s t, R s t → read s = read t)
    (decode : Result E → Option Event) :
    ∃ decoder : Public → World → Coins → Option Event,
      ∀ w os coins, ¬ bad w os coins →
        decode (observation read (client account (body w) (initial os coins))) = decoder (pub w) os coins :=
  PV_OptB_Factorization.decoder_of_off_bad pub _ bad
    (independent_off_bad pub bad account body initial R steps initial_related read preserved decode)
''')]
for a,(name,body) in enumerate(steps,44636):
 p.write_text(p.read_text().replace('end '+ns,body+'\n#print axioms '+name+'\nend '+ns))
 r=subprocess.run(['python3','evidence/pv-optb-20261027/offbad/check.py',str(a),'R1Z/PV_OptB_OffBadJoin'],capture_output=True,text=True)
 print(a,name,r.returncode,r.stdout[-2400:] if r.returncode else 'checked',flush=True)
 if r.returncode:break
