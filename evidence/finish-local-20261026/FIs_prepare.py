from pathlib import Path
import re
R=Path(__file__).resolve().parents[2]; L=R/'lean'
names='Cons_Second P2P_ResultSelected P2P_PairSelected P2P_ActualResult P2P_ActualPair P2P_ClosedResult P2P_ClosedPair P2P_DirectResult P2P_DirectPair P2P_LiteralResult P2P_LiteralPair P2P_LiteralFull P2P_LiteralTop P2P_R3Result P2P_R3Top P2P_SafResult P2P_SafTop P2P_FinalResult P2P_FinalTop P2P_Deployed P2P_Extract P2P_Source P2P_R5Result P2P_R5Close Rc7_Native P2P_R6Result P2P_Result P2P_Release'.split()
mp={n:'FIs_'+n for n in names}
for n in names:
 s=(L/(n+'.lean')).read_text()
 s=re.sub(r'\b('+ '|'.join(names)+r')\b',lambda m:mp[m[0]],s)
 s=s.replace('p2p_extract_source','fis_extract_source')
 if 'Cons_Native.Calls' in s:
  s='import FIs_Native\n'+s
  s=s.replace('Cons_Native.Calls','FIs_Native.Calls')
 if n=='Cons_Second':
  s=s.replace('Cons_NativeBuild.accepted','SAG_NativeFull.accepted').replace('⟨t,calls,aux⟩','⟨t,calls,aux,shape⟩').replace('exact ⟨t,calls,aux⟩','exact ⟨t,⟨calls,aux,shape⟩,aux⟩')
  # replacement preceding changes has transformed final exact too
  s=s.replace('exact ⟨t,calls,aux,shape⟩','exact ⟨t,⟨calls,aux,shape⟩,aux⟩')
 if n=='P2P_PairSelected':
  s=s.replace('tx2run,calls,aux⟩','tx2run,enriched,aux⟩').replace('saved f s cuts\n  refine','saved f s cuts\n  have calls := enriched.1\n  refine').replace('tx2run,origin,calls,?_','tx2run,origin,enriched,?_')
 if n=='P2P_SafResult': s=s.replace('⟩ := calls\n','⟩ := calls.1\n')
 if n=='P2P_FinalResult':s=s.replace('(reader := calls.1)','(reader := calls.1.1)')
 (L/(mp[n]+'.lean')).write_text('/- FIs same-run enrichment; read-only source: '+n+'.lean. -/\n'+s)
