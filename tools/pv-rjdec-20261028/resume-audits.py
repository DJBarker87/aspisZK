"""Freeze three new audit modules using only accepted private objects."""
from pathlib import Path
import json,re
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-rjdec-20261028';D=R/'docs/research/v8-r0-zk-20261009/lean/R1Z'
accepted={v['module']:v for p in E.glob('modules-*.json') for v in json.loads(p.read_text()) if v['accepted']};mods=sorted(m for m in accepted if m.startswith(('R1Z.PV_RJDec_','R1Z.PV_RDCD_')) and not m.endswith(('Audit','Replay')))
imports=''.join('import '+m+'\n' for m in mods)
roots=['R1Z.PV_RJDec_Runtime.source','R1Z.PV_RJDec_Runtime.executes','R1Z.PV_RJDec_MemoryInstalled.array_complete','R1Z.PV_RJDec_ReachedZero.complete','R1Z.PV_RJDec_AsmBind.complete','R1Z.PV_RJDec_ParserR12.source','R1Z.PV_RJDec_ParserR15.source','R1Z.PV_RJDec_ParserR20.source','R1Z.PV_RJDec_V047.consume','R1Z.PV_RunJoin_CommonSample32.complete_view','R1Z.PV_RunJoin_CommonObserver32.complete_pair','R1Z.PV_RJDec_Factor.exists_iff','R1Z.PV_RJDec_ResultCases.fibres_iff']
(D/'PV_RJDec_ResumeStatements.lean').write_text(imports+'import R1Z.PV_RunJoin_CommonObserver32\n'+''.join('#check @'+t+'\n' for t in roots)+'#print R1Z.PV_RDCD_ZeroWorld.Event\n#print R1Z.PV_RDCD_ZeroWorld.World\n#print R1Z.PV_RunJoin_Deployed.Runtime\n')
axioms=[]
for m in mods:
 text=(R/accepted[m]['source']['path']).read_text()
 for t in re.findall(r'^#print axioms\s+(\S+)',text,re.M):axioms.append(t if t.startswith(('R1Z.','AspisR1.')) else m+'.'+t)
axioms=list(dict.fromkeys(axioms+roots))
(D/'PV_RJDec_ResumeAxioms.lean').write_text('import R1Z.PV_RJDec_ResumeStatements\n'+''.join('#print axioms '+t+'\n' for t in axioms))
(D/'PV_RJDec_ResumeReplay.lean').write_text('import R1Z.PV_RJDec_ResumeAxioms\n'+''.join('#print axioms '+t+'\n' for t in roots[:9]))
(E/'resume-audit-manifest.json').write_text(json.dumps(dict(imports=mods,roots=roots,axioms=axioms,attempts=dict(statements=61394,axioms=61395,replay=61396)),indent=2)+'\n');print(len(mods),'accepted own imports;',len(axioms),'axiom prints')
