from pathlib import Path
import subprocess,json
E=Path(__file__).resolve().parent
ok={}
for i,t,deps in [(13,'NIG_FilledCoverage',[]),(14,'NIG_LibraLoop',[]),(15,'NIG_LibraWindow',[14]),(16,'NIG_LibraDomain',[15]),(17,'NIG_FinishInput',[]),(18,'NIG_Indices',[])]:
 if any(not ok[d]for d in deps):continue
 r=subprocess.run(['python3',str(E/'NIG_run.py'),f'NIG_L{i:03}','lean',t]);ok[i]=r.returncode==0
if not ok[18]:subprocess.run(['python3',str(E/'NIG_run.py'),'NIG_L019','lean','NIG_ShiftInspect'])
print(json.dumps(ok))
