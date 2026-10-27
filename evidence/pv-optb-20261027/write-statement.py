from pathlib import Path
p=Path('docs/research/v8-r0-zk-20261009/lean/R1Z')
s=(p/'PrivacyR1HeadlineDeployedReal.lean').read_text()
header=s[:s.index('/-- Exact adversary-only')].replace('namespace R1Z.PrivacyR1HeadlineDeployedReal','namespace R1Z.PV_OptB_Endpoint')
header='import R1Z.PrivacyR1HeadlineDeployedReal\n'+header[header.index('set_option'):]
header += '''variable {E : Type}
variable (failure : E → rust.Adversary → ROMView K CommitHandle Aux R1Bat)

def realTestB (signal : Option E) (adv : rust.Adversary) (w : (h).Instance) :
    rust.RealRand → ℚ :=
  match signal with
  | none => realTest h B outputs rust adv x w
  | some e => fun _ => bit (rust.observe adv (failure e adv))

def idealTestSB (signal : Option E) (adv : rust.Adversary) :
    (source).IdealRand → ℚ :=
  match signal with
  | none => idealTestS source (RomObserverBin.observerMap rust observer_program adv) x
      (simE (h).transport B outputs x)
  | some e => fun _ => bit (rust.observe adv (failure e adv))

'''
start=s.index('theorem privacy_headline_deployed')
end=s.index(' := by',start)
stmt=s[start:end].replace('privacy_headline_deployed','privacy_headline_deployed_B',1).replace('(refinement : RustRealRefinement','(refinement : PrivacyR1HeadlineDeployedReal.RustRealRefinement')
stmt=stmt.replace(' :\n    (∀',' (signal : Option E) :\n    (∀',1)
stmt=stmt.replace('realTest h B outputs rust adv x w','realTestB template outputs x rust failure signal adv w')
stmt=stmt.replace('idealTestS source (RomObserverBin.observerMap rust observer_program adv) x\n          (simE (h).transport B outputs x)','idealTestSB template outputs x rust observer_program failure signal adv')
proof=''' := by
  have old := PrivacyR1HeadlineDeployedReal.privacy_headline_deployed
    template outputs x rust observer_program refinement
  refine ⟨?_, old.2⟩
  intro adv w hw
  cases signal with
  | none => exact old.1 adv w hw
  | some e =>
    simp only [realTestB, idealTestSB, mean_const, sub_self, abs_zero]
    exact (abs_nonneg _).trans (old.1 adv w hw)

#print PrivacyR1HeadlineDeployedReal.privacy_headline_deployed
#print privacy_headline_deployed_B
#print axioms realTestB
#print axioms idealTestSB
#print axioms privacy_headline_deployed_B
end R1Z.PV_OptB_Endpoint
'''
(p/'PV_OptB_Endpoint.lean').write_text(header+stmt+proof)
