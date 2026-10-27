from pathlib import Path
import re
L=Path(__file__).resolve().parents[2]/'lean'
orig=(L/'FIs_Caller.lean').read_text()
head=orig[:orig.index('def Outcome')].replace('namespace AspisR1.FIs_Caller','namespace AspisR1.FJp_ActualCaller')
head='import FIs_Caller\nimport FJp_ActualCont\n'+head
defs=orig[orig.index('def Outcome'):orig.index('theorem strengthen')].replace('FIs_Cont.Outcome','FJp_ActualCont.Outcome')
sig=orig[orig.index('theorem strengthen'):orig.index('    {Hash :')]
sig=sig.replace('theorem strengthen {W F CoreError : Type}','theorem strengthen {W C : Type} (err : C) (seed : DrvC_Installation.Configuration FIo_Install.W C)\n    (r : NP6_StdModel.Reservation)')
a=sig.index('    (adapterOps :');b=sig.index('    (B :',a);sig=sig[:a]+sig[b:]
cfg='(FIp_Install.configuration err seed r)'
mp={'adapterOps':cfg+'.adapter','ops':cfg+'.currentBase','reserved':cfg+'.reserved','queryOps':cfg+'.query','geoOps':cfg+'.geometry','stageBase':cfg+'.stageBase','finishOps':cfg+'.finish'}
sig=re.sub(r'\b('+ '|'.join(mp)+r')\b',lambda m:mp[m[0]],sig)
# Native extraction/cut types exactly as the checked actual-cont consumer.
ac=(L/'FJp_ActualCont.lean').read_text()
a=ac.index('    (accounts1 accounts2');b=ac.index('    (native1 :',a)
cut=ac[a:b];cut=cut[cut.index('    (cuts :'):].replace('accounts1 accounts2 saved f s','e1.first (e2.second secondSizes) saved f s')
a=ac.index('    (native1 :');b=ac.index('    (sameProof :',a)
extras=ac[a:b]
args=f'L e1 e2 w1 w2 {cfg}.adapter {cfg}.currentBase {cfg}.reserved {cfg}.query {cfg}.geometry {cfg}.stageBase {cfg}.finish B claimsStd program data1 data2 slot saved post1 post2 H f s outer pre middle fs ss run prior tx2'
body='''    (rootBinding : FJp_RootBinding.Holds f.proof run.root)
    (old : FIs_Caller.Outcome '''+args+''') :
    Outcome '''+args+''' := by
  let c := FIp_Install.configuration err seed r
  obtain ⟨parsed,facts,sites,cont⟩ := old
  have reachedTx2 := S2W_SiteSchedule.reached pre middle fs ss .tx2
  have sameProof : bytesOf s.proof.val=bytesOf f.proof.val := by
    simpa only [S2W_InputSchedule.observation,show ¬ S2LeadInterface.Site.tx2.rank ≤ 3 by decide,if_false] using facts.proofBytes .tx2 reachedTx2
  have sameSaved : bytesOf s.checkpoint.val=bytesOf saved.val := by
    simpa only [S2W_InputSchedule.observation,show ¬ S2LeadInterface.Site.tx2 = .save by decide,if_false] using facts.checkpointBytes .tx2 reachedTx2 (Or.inr (Or.inl rfl))
  have size : f.proof.val.length=57607 := by
    simpa only [bytesOf,List.length_map] using facts.proofLength
  refine ⟨parsed,facts,sites,?_⟩
  exact FJp_ActualCont.strengthen err seed r B claimsStd saved f s run prior H tx2 e1.first
    (e2.second secondSizes) cuts native1 native2 hashv extraction sha256 p1 syscall sameProof sameSaved size rootBinding cont
#print axioms strengthen
end AspisR1.FJp_ActualCaller
end
'''
(L/'FJp_ActualCaller.lean').write_text(re.sub(r'\bstd\b','claimsStd',head+defs+sig+cut+extras+body))
