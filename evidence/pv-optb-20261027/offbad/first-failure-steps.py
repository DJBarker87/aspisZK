from step import check,append
m='R1Z/PV_OptB_FirstFailureOffBad';ns='R1Z.PV_OptB_FirstFailureOffBad'
check(m)
append(m,ns,'signal_pair','''theorem signal_pair
    (runtime : PV_RunJoin_Deployed.Runtime CommitHandle Aux Coins N L C)
    (h : HonestProver K) (x : Statement K CommitHandle)
    (r : PV_RunJoin_Deployed.World runtime)
    (fault : PV_OptB_RuntimeFirstDraw.FirstDrawFailure runtime r) (w u : h.Instance)
    (decode : Result (PV_RunJoin_Deployed.Output N L C) → Option Event) :
    decode (PV_RunJoin_Deployed.execute runtime h x w r) =
      decode (PV_RunJoin_Deployed.execute runtime h x u r) :=
  congrArg decode (execute_pair runtime h x r fault w u)
''')
append(m,ns,'independent_off_bad_on_first_failures','''theorem independent_off_bad_on_first_failures
    (runtime : PV_RunJoin_Deployed.Runtime CommitHandle Aux Coins N L C)
    (h : HonestProver K) (x : Statement K CommitHandle)
    (decode : Result (PV_RunJoin_Deployed.Output N L C) → Option Event)
    (bad : h.Instance →
      (Σ r : PV_RunJoin_Deployed.World runtime, PV_OptB_RuntimeFirstDraw.FirstDrawFailure runtime r) → Unit → Prop) :
    PV_OptB_Factorization.IndependentOffBad h.public
      (fun w (r : Σ r : PV_RunJoin_Deployed.World runtime, PV_OptB_RuntimeFirstDraw.FirstDrawFailure runtime r)
        (_ : Unit) => decode (PV_RunJoin_Deployed.execute runtime h x w r.1)) bad :=
  PV_OptB_Factorization.independent_implies_off_bad h.public _ bad
    (PV_OptB_FirstWorldSignal.independent_on_first_failures runtime h x decode)
''')
