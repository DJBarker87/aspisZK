from pathlib import Path
L=Path('lean')
s=(L/'Rc6_Caller.lean').read_text();s=s[:s.index('theorem from_cut')];s=s.replace('AspisR1.Rc6_Caller','AspisR1.P2P_Caller').replace('      P2Prime H f.proof f.pub s.proof s.pub →\n','');s+='end AspisR1.P2P_Caller\nend\n';(L/'P2P_Caller.lean').write_text(s)
s=(L/'CPP_Acceptance.lean').read_text().replace('AspisR1.CPP_Acceptance','AspisR1.P2P_Acceptance');s=s.replace('    ∀ (p2prime : S2W_AuthenticatedInputs.P2Prime H proof pub proof2 pub2),\n','');(L/'P2P_Acceptance.lean').write_text(s)
s=(L/'P2P_R6Result.lean').read_text();s=s[:s.index('theorem strengthen')];s=s.replace('AspisR1.P2P_R6Result','AspisR1.P2P_Result')
s='import P2P_Caller\nimport P2P_Acceptance\n'+s
s=s.replace('(hashv : S2Z.Oracle.Parts → Result S2Z.Oracle.Digest) : Prop :=','(hashv : S2Z.Oracle.Parts → Result S2Z.Oracle.Digest) (bad : Prop) : Prop :=')
start=s.index('      CPP_Acceptance.Facts');end=s.index('      PFin_Packet.Facts',start)
# Keep ungated facts before the single collision alternative.
accept=s[start:end]
s=s[:start]+s[end:]
s=s.replace('      Rc6_Caller.Outcome','      (bad ∨\n'+accept.replace('CPP_Acceptance.Facts','P2P_Acceptance.Facts').replace('Rc5_Nonvacuity.Facts','P2P_Acceptance.Facts')+'      P2P_Caller.Outcome')
s=s.rstrip()+')\nend AspisR1.P2P_Result\nend\n'
(L/'P2P_Result.lean').write_text(s)
