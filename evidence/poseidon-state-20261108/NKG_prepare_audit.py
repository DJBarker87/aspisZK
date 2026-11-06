from pathlib import Path
import json,re,hashlib,difflib
E=Path(__file__).resolve().parent;B='/home/dombarker/project-offloads/codex-cx-poseidon-state-20261108'
T='/home/dombarker/.elan/toolchains/leanprover--lean4---v4.32.0'
ats=[json.loads(l)for l in(E/'NKG_ATTEMPTS.jsonl').read_text().splitlines()];last={a['module']:a for a in ats if a['kind']=='lean'}
modules=[];roots=['AspisR1.RPx_Deployed.deployed'];pins={}
for p in sorted((E/'NKG_lean').glob('NKG_*.lean')):
 if p.stem.startswith('NKG_COMBINED')or p.stem in ['NKG_EmittedView','NKG_Driver','NKG_ProofDriver']:continue
 a=last.get(p.stem);assert a and a['exit_status']==0,('uncompiled',p.stem)
 snap=E/a['attempt']/'sources/NKG_lean'/p.name;assert snap.read_bytes()==p.read_bytes(),p.name
 modules.append(p.stem);ns=re.findall(r'^namespace (\S+)',p.read_text(),re.M)[0]
 for n in re.findall(r'^#print axioms (\S+)',p.read_text(),re.M):roots.append(n if n.startswith(ns+'.')else ns+'.'+n)
 pins[p.stem]=dict(source_sha256=hashlib.sha256(p.read_bytes()).hexdigest(),attempt=a['attempt'])
imports=['NKC_COMBINED_IMPORT']+modules
mainroots=['AspisR1.NKG_ColumnsPacket.source','AspisR1.NKG_InternalPacket.source','AspisR1.NKG_FullPacket.source','AspisR1.NKG_OraclePacket.source']
body=''.join('import '+m+'\n'for m in imports)+'\n#check AspisR1.RPx_Deployed.deployed\n#print axioms AspisR1.RPx_Deployed.deployed\n'+''.join('#print '+r+'\n#print axioms '+r+'\n'for r in mainroots)
for m in ['AspisR1.NKG_ColumnCuts.Step','AspisR1.NKG_ColumnCuts.Trace','AspisR1.NKG_HelperCuts.Internal','AspisR1.NKG_HelperCuts.Full','AspisR1.NKG_PreludeFrame.Cut','AspisR1.NKG_LowFrame.Trace','AspisR1.NKG_LowFrame.Steps','AspisR1.NKG_GroupFrame.Frame','AspisR1.NKG_OracleCuts.Prepare','AspisR1.NKG_OracleCuts.Pack','AspisR1.NKG_OracleCuts.Sub','AspisR1.NKG_OracleCuts.Sum','AspisR1.NKG_OracleCuts.Mul','AspisR1.NKG_OracleCuts.Output']:body+='#print '+m+'\n'
(E/'NKG_COMBINED_IMPORT.lean').write_text(body);(E/'NKG_lean/NKG_COMBINED_IMPORT.lean').write_text(body)
expected={x['module']:x['imports']for x in map(json.loads,(E.parent/'ledger17-20261108/NKC_EXPECTED_IMPORTS.jsonl').read_text().splitlines())}
expected['NKG_COMBINED_IMPORT']=['Init']+imports
for m in modules:expected[m]=['Init']+re.findall(r'^import (\S+)',(E/'NKG_lean'/f'{m}.lean').read_text(),re.M)
for name in ['Driver','ProofDriver']:
 src=E.parent/'ledger17-20261108'/f'NKC_{name}.lean';old=src.read_text();new=old.replace('NKC_','NKG_')
 (E/'NKG_lean'/f'NKG_{name}.lean').write_text(new)
 (E/f'NKG_{name}.diff').write_text(''.join(difflib.unified_diff(old.splitlines(True),new.splitlines(True),fromfile=str(src),tofile='NKG_'+name+'.lean')))
 expected['NKG_'+name]=['Init']+re.findall(r'^import (\S+)',new,re.M)
(E/'NKG_EXPECTED_IMPORTS.jsonl').write_text(''.join(json.dumps(dict(module=m,imports=im))+'\n'for m,im in sorted(expected.items())))
roots=list(dict.fromkeys(roots));(E/'NKG_AUDIT_ROOTS.json').write_text(json.dumps(dict(roots=roots,groups=[roots]),indent=2)+'\n');(E/'NKG_AUDIT_MODULES.json').write_text(json.dumps([['NKG_COMBINED_IMPORT']],indent=2)+'\n')
(E/'NKG_PROOF_INVENTORY.json').write_text(json.dumps(dict(modules=pins,roots=roots,main_roots=mainroots,inspection_only=['NKG_EmittedView'],failed_receipts_excluded=True),indent=2)+'\n')
base=json.loads((E/'NKG_L001.json').read_text())
for num,m in [(47,'NKG_Driver'),(48,'NKG_ProofDriver'),(51,'NKG_COMBINED_IMPORT')]:
 a=f'NKG_L{num:03}';x=json.loads(json.dumps(base));x.update(attempt=a,module=m,sources=['NKG_lean/'+m+'.lean'],upload=['NKG_lean/'+m+'.lean'],expected_time='Focused audit driver compilation'if num<50 else 'First full combined NKC/headline import; print complete four packet roots and cut definitions')
 x['command']=[T+'/bin/lake','env','lean','-j1','-M7000','-DElab.async=false','-o','NKG_objects/'+m+'.olean','NKG_lean/'+m+'.lean']
 if num<50:x['command']+=['-c','NKG_native/'+m+'.c']
 (E/(a+'.json')).write_text(json.dumps(x,indent=2)+'\n')
for num,m in [(49,'NKG_Driver'),(50,'NKG_ProofDriver')]:
 a=f'NKG_L{num:03}';x=json.loads(json.dumps(base));x.update(attempt=a,kind='link',module=m,sources=['NKG_native/'+m+'.c','NKG_native/NKG_WALKER.c','NKG_native/NKG_MemoryLimit.c'],upload=['NKG_native/NKG_WALKER.c','NKG_native/NKG_MemoryLimit.c'],expected_time='Optimized linker; unchanged admitted NFA C walker and memory-limit helper')
 x['command']=[T+'/bin/lake','env','leanc','-O3','-rdynamic','-o','NKG_native/'+m,*x['sources']]
 (E/(a+'.json')).write_text(json.dumps(x,indent=2)+'\n')
for num,mode in [(52,'fixtures'),(53,'scan'),(54,'proof0')]:
 a=f'NKG_L{num:03}';x=json.loads(json.dumps(base));files=['NKG_audit.py','NKG_AUDIT_ROOTS.json','NKG_AUDIT_MODULES.json','NKG_EXPECTED_IMPORTS.jsonl'];x.update(attempt=a,kind='audit',module=mode,sources=files,upload=files,collect=[a+'_validation']+(['NKG_LOADED_scan.jsonl']if mode=='scan'else []),expected_time='Same-binary eight fidelity fixtures'if mode=='fixtures'else 'NFX full imported-closure coherence scan'if mode=='scan'else 'Raw ax2 walk of every new accepted top theorem plus deployed headline')
 x['command']=['python3','NKG_audit.py',mode,a]
 (E/(a+'.json')).write_text(json.dumps(x,indent=2)+'\n')
print(json.dumps(dict(modules=len(modules),roots=len(roots),audits_prepared=1)))
