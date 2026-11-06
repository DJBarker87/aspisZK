"""Prepare (do not launch) the second and final combined gate."""
from pathlib import Path
import hashlib,json,re,copy
E=Path(__file__).resolve().parent
attempts=[json.loads(l) for l in (E/'NJE_ATTEMPTS.jsonl').read_text().splitlines()]
modules=['NJE_ArityPackets','NJE_ReadPackets','NJE_RootPackets','NJE_Pow5Packet','NJE_Mat4Packet','NJE_ExternalBlocks','NJE_ParentPackets','NJE_WellFrozen','NJE_LinearPackets','NJE_CountPacket','NJE_ConstantShifts','NJE_ConstantsInitial','NJE_ConstantsInternal','NJE_ConstantsFinal','NJE_PermutationFold','NJE_RoundComposition']
for optional in ['NJE_InternalRound','NJE_RoundTrace','NJE_CompressSeed']:
 if any(a.get('module')==optional and a.get('exit_status')==0 for a in attempts):modules.append(optional)
selected={}
def visit(module):
 if module in selected:return
 f=E/'NJE_lean'/(module+'.lean');assert f.exists(),module
 src=f.read_text();imports=re.findall(r'^import\s+(?:all\s+)?([\w.]+)',src,re.M)
 successes=[a for a in attempts if a.get('module')==module and a.get('exit_status')==0 and a.get('kind')=='lean']
 assert successes,module+' has no positive focused compile'
 # Match the retained source snapshot byte for byte, not a filename-only credit.
 matching=[]
 for a in successes:
  old=E/a['attempt']/'sources'/'NJE_lean'/(module+'.lean')
  if old.exists() and old.read_bytes()==f.read_bytes():matching.append(a['attempt'])
 assert matching,module+' differs from every positive source snapshot'
 selected[module]=dict(source=str(f.relative_to(E)),sha256=hashlib.sha256(f.read_bytes()).hexdigest(),focused=matching[-1],imports=imports)
 for imp in imports:
  if imp.startswith('NJE_'):visit(imp)
for module in modules:visit(module)
combined='\n'.join('import '+m for m in ['NGK_COMBINED_IMPORT','NIU_COMBINED_IMPORT','NJA_COMBINED_IMPORT']+modules)+'\n\n#check AspisR1.RPx_Deployed.deployed\n#print axioms AspisR1.RPx_Deployed.deployed\n#print NJE_CountPacket.assoc\n#print axioms NJE_CountPacket.assoc\n'
(E/'NJE_COMBINED_IMPORT.lean').write_text(combined)
(E/'NJE_lean/NJE_COMBINED_IMPORT.lean').write_text(combined)
base={r['module']:r for r in [json.loads(l) for l in (E/'NJE_GATE1_EXPECTED_IMPORTS.jsonl').read_text().splitlines()]}
for module,v in selected.items():base[module]=dict(module=module,imports=list(dict.fromkeys(['Init']+v['imports'])))
base['NJE_COMBINED_IMPORT']=dict(module='NJE_COMBINED_IMPORT',imports=['Init']+['NGK_COMBINED_IMPORT','NIU_COMBINED_IMPORT','NJA_COMBINED_IMPORT']+modules)
(E/'NJE_EXPECTED_IMPORTS.jsonl').write_text(''.join(json.dumps(base[m],sort_keys=True)+'\n' for m in sorted(base)))
roots=['AspisR1.RPx_Deployed.deployed','NJE_CountPacket.assoc']
for module,v in selected.items():
 src=(E/v['source']).read_text()
 ns=re.search(r'^namespace\s+(NJE_[\w.]+)',src,re.M)
 namespace=ns.group(1) if ns else ''
 for name in re.findall(r'^#print axioms\s+([\w.]+)',src,re.M):
  full=name if name.startswith(('NJE_','AspisR1.')) else namespace+'.'+name
  if full not in roots:roots.append(full)
groups=[roots[::2],roots[1::2]]
(E/'NJE_AUDIT_ROOTS.json').write_text(json.dumps(dict(roots=roots,groups=groups),indent=2)+'\n')
(E/'NJE_AUDIT_MODULES.json').write_text(json.dumps([['NJE_COMBINED_IMPORT'] for g in groups],indent=2)+'\n')
(E/'NJE_SELECTED_MODULES.json').write_text(json.dumps(dict(roots=modules,dependency_closure=selected,axiom_roots=roots,combined_audit=2),indent=2)+'\n')
# Preserve gate-one inputs; final snapshots are frozen now.
for name in ['NJE_COMBINED_IMPORT.lean','NJE_EXPECTED_IMPORTS.jsonl','NJE_AUDIT_ROOTS.json','NJE_AUDIT_MODULES.json']:
 (E/('NJE_GATE2_'+name.removeprefix('NJE_'))).write_bytes((E/name).read_bytes())
for index,(source,kind,module,command,collect) in enumerate([
 ('NJE_L013.json','lean','NJE_COMBINED_IMPORT',None,[]),
 ('NJE_L014.json','audit','NJE_scan',['NJE_native/NJE_Driver','scan'],['NJE_LOADED_scan.jsonl']),
 ('NJE_L016.json','audit','NJE_raw0',['NJE_native/NJE_ProofDriver','proof0'],[]),
 ('NJE_L016.json','audit','NJE_raw1',['NJE_native/NJE_ProofDriver','proof1'],[])],97):
 c=copy.deepcopy(json.load(open(E/source)));c.update(attempt=f'NJE_L{index:03}',kind=kind,module=module)
 if command:c['command']=command
 c['collect']=collect
 c['expected_time']='Final combined gate '+module+'; coherent reused objects, canonical unchanged walker; not cold/full release replay'
 (E/f'NJE_L{index:03}.json').write_text(json.dumps(c,indent=2)+'\n')
print('Prepared FINAL combined audit: '+str(len(selected))+' own modules, '+str(len(roots))+' raw axiom roots in2 groups; no launch.')
