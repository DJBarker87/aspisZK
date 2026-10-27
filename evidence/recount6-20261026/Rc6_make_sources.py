from pathlib import Path
L=Path('lean')
# Keep Rc5 continuation and eliminate only its already derivable entry guard.
s=(L/'Rc5_Caller.lean').read_text(); head=s.split('def Outcome')[0].replace('namespace AspisR1.Rc5_Caller','namespace AspisR1.Rc6_Caller')
defn=s.split('def Outcome')[1].split('theorem strengthen')[0]
defn=defn.replace('      S2W_ChildJoins.FirstEntryVerifierConeJoin f.proof →\n','')
t=(L/'PFin_BoundCaller.lean').read_text().split('theorem from_cut')[1].split('\n#print axioms')[0]
t=t.replace('(old : T2R_CallerSource.Outcome','(old : Rc5_Caller.Outcome').replace('geoOps B claimsStd','geoOps (F3M_CircleSource.install B) claimsStd')
# Adjust run binder too; B in the theorem describes the original, pre-circle boundary.
t=t.replace('geoOps B claimsStd)', 'geoOps (F3M_CircleSource.install B) claimsStd)')
t=t.replace(':= by\n',':= by\n',1)
t=t.replace('  intro history p2prime','  intro p2prime').replace('old history p2prime entry','old p2prime entry')
t=t.replace('PFin_Attach.from_cut adapterOps ops reserved queryOps geoOps stageBase finishOps B claimsStd','PFin_Attach.from_cut adapterOps ops reserved queryOps geoOps stageBase finishOps (F3M_CircleSource.install B) claimsStd')
start=t.index('  have tx2Reached')
t=t[:start]+'''  exact ⟨parsed,facts,sites,cont⟩'''
# Calls to Outcome/old require original B (not the installed circle); only dictionary/run need circle.
t=t.replace('stageBase finishOps B claimsStd\n      program','stageBase finishOps B claimsStd\n      program')
(L/'Rc6_Caller.lean').write_text('import PFin_Attach\nimport Rc5_Caller\n'+head+'def Outcome'+defn+'theorem from_cut'+t+'\n\n#print axioms from_cut\nend AspisR1.Rc6_Caller\nend\n')
