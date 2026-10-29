from pathlib import Path
import json,re
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-runjoin51-20261029';L=R/'docs/research/v8-r0-zk-20261009/lean/R1Z'
accepted={v['module']:v for p in E.glob('modules-*.json') for v in json.loads(p.read_text()) if v['accepted']}
# Reserve source not yet launched only after its matching acceptance exists.
assert 'R1Z.PV_RunJoin_MaterialAlphaFixed51' in accepted
mods=sorted(m for m in accepted if m.startswith('R1Z.PV_RunJoin_') and m.endswith('51'))
names=[]
for m in mods:
 p=L/(m.split('.')[-1]+'.lean');s=p.read_text();ns=re.search(r'^namespace\s+(\S+)',s,re.M)[1]
 for n in re.findall(r'^#print axioms\s+(\S+)',s,re.M):names.append(n if n.startswith('R1Z.') else ns+'.'+n)
focus=['CommonSemanticSource51','CommonScalar51','MaterialSourceFields51','PrepareOrigins51','MaterialAlphaFixed51']
s='\n'.join('import R1Z.PV_RunJoin_'+m for m in focus)+'\nset_option autoImplicit false\n'
for m,n in [('CommonOracle51','read'),('CommonSemanticSource51','complete'),('CommonScalar51','complete'),('MaterialSourceFields51','complete'),('PrepareOrigins51','complete')]:
 s+=f'#print R1Z.PV_RunJoin_{m}.{n}\n#print axioms R1Z.PV_RunJoin_{m}.{n}\n'
(L/'PV_RunJoin_ModelAudit51.lean').write_text(s)
s='import R1Z.PV_RunJoin_ModelAudit51\nimport R1Z.PV_RunJoin_CombinedAudit50\n'+'\n'.join('import '+m for m in mods)+'\nset_option autoImplicit false\n'
s+='\n'.join('#print axioms '+n for n in sorted(set(names)))+'\n'
(L/'PV_RunJoin_CombinedAudit51.lean').write_text(s)
als=['PV_AL_CircleCarriers','PV_AL_ShiftLiterals','PV_AL_CircleControl','PV_AL_CircleNative','PV_AL_CircleSelected'];alnames=[]
for m in als:
 s=(L/(m+'.lean')).read_text();ns=re.search(r'^namespace\s+(\S+)',s,re.M)[1]
 for n in re.findall(r'^#print axioms\s+(\S+)',s,re.M):alnames.append(n if n.startswith('R1Z.') else ns+'.'+n)
s='import R1Z.PV_AL_CircleSelected\nimport R1Z.PV_AL_ShiftLiterals\nset_option autoImplicit false\n'+'\n'.join('#print axioms '+n for n in sorted(set(alnames)))+'\n'
(L/'PV_RunJoin_CircleAudit51.lean').write_text(s)
(E/'audit-plan.json').write_text(json.dumps(dict(model='R1Z.PV_RunJoin_ModelAudit51',combined_model='R1Z.PV_RunJoin_CombinedAudit51',isolated_circle='R1Z.PV_RunJoin_CircleAudit51',model_modules=mods,model_names=sorted(set(names)),circle_names=sorted(set(alnames)),excluded=['R1Z.PV_RunJoin_CircleInstalled51'],cohort_conflict='circle-cohort-finding.json; no joint model/circle import credited'),indent=2)+'\n')
print('Model modules',len(mods),'printed names',len(set(names)),'isolated circle printed names',len(set(alnames)))
