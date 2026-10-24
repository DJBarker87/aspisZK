"""Read-only current-source pins and selected unchanged dependency assessment."""
from pathlib import Path
import json,hashlib,subprocess
R=Path(__file__).resolve().parents[2];L=R/'docs/research/100bit-spend-path-20261013/lean';E=R/'evidence/port9oracle-20261024'
def info(p):return {'sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'bytes':p.stat().st_size}
files=[Path('programs/r1-cost-probe/src/lib.rs'),Path('crates/aspis-core/src/digest.rs'),Path('crates/aspis-r1-cost-probe/src/candidate.rs')]
records={str(p):info(R/p) for p in files}
for p in sorted(L.glob('Port9OR_*.lean')):records[str(p.relative_to(R))]=info(p)
reused=['Port8EFF_NativeReader','Port8EFF_Bodies','Port8EFF_CheckpointCode','Port6CK_Reader','Port6CK_Ops','Port7CLEAN_Driver','Port7CLEAN_TraceObstruction','Port6AUTH_Prefix','Port6AUTH_Probability','Port6AUTH_Headline','S2W_DigestExtraction','Port4B_Install','Port3_NativeBatchBody','Port4B_LeafCode','MultiproofConeRef/Funs']
assessment={m:{**info(L/(m+'.lean')),'assessment':'Reused unchanged source and cached compiled dependencies; focused compilation is not a coherent release identity gate.'} for m in reused}
x={'revision':subprocess.check_output(['git','rev-parse','HEAD'],cwd=R,text=True).strip(),'current_sources':records,'reused_dependencies':assessment,'elf_pins':{'default':'f8c0ec72621fd5029a97d796c4a3623d0dc44a8e7074122372f9872915d143d4','devnet':'63ad3e9cc096dcbb55b3ca7ac7c8e89e6a845796ab5e4f5b7d15db96f3784299','pool':'121f3e29741f510e6dc42d0345fc3c36217600f0be337094855c4a9da2581548'},'new_identity_gate':False,'source_changes_authorized':'New Port9OR proof modules and source-extraction prototypes only; no crates/programs modifications.'}
(E/'source-assessment.json').write_text(json.dumps(x,indent=2)+'\n')
