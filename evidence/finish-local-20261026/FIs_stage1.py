from pathlib import Path
import subprocess
P=Path(__file__).resolve().parent
mods='Cons_Second P2P_ResultSelected P2P_PairSelected P2P_ActualResult P2P_ActualPair P2P_ClosedResult P2P_ClosedPair P2P_DirectResult P2P_DirectPair P2P_LiteralResult P2P_LiteralPair P2P_LiteralFull P2P_LiteralTop P2P_R3Result P2P_R3Top P2P_SafResult P2P_SafTop P2P_FinalResult P2P_FinalTop P2P_Deployed P2P_Extract P2P_Source P2P_R5Result P2P_R5Close Rc7_Native P2P_R6Result P2P_Result P2P_Release'.split()
for n,m in enumerate(mods,2):
 print(n,m,flush=True)
 r=subprocess.run(['python3',str(P/'FIs_compile.py'),str(n),'FIs_'+m])
 if r.returncode:break
