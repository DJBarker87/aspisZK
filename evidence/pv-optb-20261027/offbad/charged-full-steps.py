from step import append
m='R1Z/PV_OptB_Charged';ns='R1Z.PV_OptB_Charged'
common='fullUnion h P V W Pr R N hN B outputs x ab adv c M q charged priv qry addr core'
append(m,ns,'off_full_auxiliary',f'''theorem off_full_auxiliary (v : h.Instance) (world : World) (random : Coins)
    (good : ¬ {common} v world random) :
    ¬ union h P V W Pr R N hN B outputs x ab adv c v world random :=
  fun event => good (Or.inl event)
''')
append(m,ns,'off_full_hit',f'''theorem off_full_hit (v : h.Instance) (world : World) (random : Coins)
    (good : ¬ {common} v world random) :
    ¬ R0Z.FsAbortBounds.HitEv M q charged qry addr (core v world random) :=
  fun event => good (Or.inr (Or.inl event))
''')
append(m,ns,'off_full_collision',f'''theorem off_full_collision (v : h.Instance) (world : World) (random : Coins)
    (good : ¬ {common} v world random) :
    ¬ R0Z.FsAbortBounds.CollEv M priv addr (core v world random) :=
  fun event => good (Or.inr (Or.inr event))
''')
