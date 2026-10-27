from pathlib import Path
import re,json
R=Path(__file__).resolve().parents[2];P=Path(__file__).resolve().parent
files=sorted(p for p in (R/'lean').glob('FIq_*.lean') if p.stem!='FIq_FinalClosure')
reports=[]
for p in files:
 code=re.sub(r'/--.*?-/|/-.*?-/', '',p.read_text(),flags=re.S)
 namespaces=re.findall(r'^namespace\s+([\w.]+)',code,re.M)
 if not namespaces:continue
 assert len(namespaces)==1,(p,namespaces)
 for name in re.findall(r'^(?:@\[[^\n]*\]\s*)?theorem\s+([\w.]+)',code,re.M):
  reports.append(namespaces[0]+'.'+name)
lines=['import '+p.stem for p in files]+['set_option pp.proofs false']
lines+=['#print axioms '+name for name in dict.fromkeys(reports)]
lines+=['#print axioms FIq_Native.pool_v1.pair_forest_semantic_terminal.r0.Public.terminal_qm31']
(R/'lean/FIq_FinalClosure.lean').write_text('\n'.join(lines)+'\n')
(P/'FIq_axiom-targets.json').write_text(json.dumps(dict(modules=[p.stem for p in files],public_theorems=list(dict.fromkeys(reports)),note='All final new-module public theorems, plus complete retained terminal body; private proof dependencies are included transitively in top reports.'),indent=2)+'\n')
print('modules',len(files),'public theorem reports',len(reports))
