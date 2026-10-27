import pathlib,subprocess
p=pathlib.Path('docs/research/v8-r0-zk-20261009/lean/R1Z/PV_OptB_Charged.lean');ns='R1Z.PV_OptB_Charged'
header='''
variable (c : Coordinates h W Pr N ab World Coins)
  (w : h.Instance) (os : World) (coins : Coins)
'''
p.write_text(p.read_text().replace('end '+ns,header+'end '+ns))
events=[('pole','poleBad P h V ab adv x w (c.retry w os coins)'),('lazy','QueryScanRealLazyBound.lazyBad W Pr R N hN h B outputs x w (c.lazy w os coins)'),('mask','FinalR1PBin.exhQ W Pr R N hN h B outputs x w (c.lazy w os coins)'),('fresh','QueryScanRealFreshMass.realFresh W Pr N h B outputs x w (c.real w os coins)'),('parser','(∃ i, QueryScanRealLazyBound.realBad W Pr N h B outputs x w i (c.real w os coins))'),('seed','ProverCommitSeedEvent19.seedGuess (c.queries w os coins) (c.seed os coins)'),('fuel','(∃ j, ProverCommitFuelJoin22.failure j (c.fuel os coins))')]
for a,(label,event) in enumerate(events,44628):
 i=a-44628;term='event'
 if i<6:term='Or.inl ('+term+')'
 for _ in range(i):term='Or.inr ('+term+')'
 body=f'''theorem off_{label} (good : ¬ union h P V W Pr R N hN B outputs x ab adv c w os coins) :
    ¬ {event} := by
  intro event
  exact good ({term})
#print axioms off_{label}
'''
 p.write_text(p.read_text().replace('end '+ns,body+'end '+ns))
 r=subprocess.run(['python3','evidence/pv-optb-20261027/offbad/check.py',str(a),'R1Z/PV_OptB_Charged'],capture_output=True,text=True)
 print(a,label,r.returncode,r.stdout[-1700:] if r.returncode else r.stdout.splitlines()[0][:150],flush=True)
 if r.returncode:break
