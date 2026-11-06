from pathlib import Path
import json,re,hashlib,subprocess,difflib
E=Path(__file__).resolve().parent
mods=['NJZ_Readers','NJZ_Weights','NJZ_Validator','NJZ_CheckpointReaders','NJZ_EmptyTree','NJZ_TreeParent','NJZ_Echeck','NJZ_CodecProjection','NJZ_CodecSemantics','NJZ_PoolRoot']
roots=[]
for m in mods:
 s=E.joinpath(m+'.lean').read_text()
 for n in re.findall(r'^theorem (\w+)',s,re.M):
  assert '#print axioms '+n in s,(m,n)
  roots.append(m+'.'+n)
 assert not re.search(r'\b(sorry|axiom|admit|native_decide)\b',s),(m,'forbidden proof token')
roots+=['AspisR1.RPx_Deployed.deployed']
E.joinpath('NJZ_AUDIT_ROOTS.json').write_text(json.dumps(dict(groups=[roots[i:i+10] for i in range(0,len(roots),10)]),indent=2)+'\n')
E.joinpath('NJZ_MODULES.json').write_text(json.dumps(mods,indent=2)+'\n')
E.joinpath('NJZ_COMBINED_IMPORT.lean').write_text('import NJW_COMBINED_IMPORT\nimport NJR_COMBINED_IMPORT\n'+''.join('import '+m+'\n' for m in mods)+'\n'+''.join('#print '+r+'\n#print axioms '+r+'\n' for r in roots))
s=Path('evidence/tx2-native7-20261108/NJR_ProofDriver.lean').read_text();a=s.index('    else if mode == "proof0"');b=s.index('    else (#[], #[])',a)
t=''
for i,g in enumerate(json.load(open(E/'NJZ_AUDIT_ROOTS.json'))['groups']):t+=f'    else if mode == "proof{i}" then\n      (#[`NJZ_COMBINED_IMPORT], #['+', '.join('`'+r for r in g)+'])\n'
E.joinpath('NJZ_ProofDriver.lean').write_text(s[:a]+t+s[b:])
expected={json.loads(l)['module']:json.loads(l) for l in E.joinpath('NJZ_EXPECTED_IMPORTS.jsonl').read_text().splitlines()}
for m in mods+['NJZ_COMBINED_IMPORT']:
 expected[m]=dict(module=m,imports=['Init']+re.findall(r'^import ([\w.]+)',E.joinpath(m+'.lean').read_text(),re.M))
E.joinpath('NJZ_EXPECTED_IMPORTS.jsonl').write_text(''.join(json.dumps(v)+'\n' for v in expected.values()))
for stem in ['ProofDriver','Driver']:
 original=Path('evidence/tx2-native7-20261108/NJR_'+stem+'.lean').read_text();current=E.joinpath('NJZ_'+stem+'.lean').read_text()
 E.joinpath('NJZ_'+stem+'.diff').write_text(''.join(difflib.unified_diff(original.splitlines(True),current.splitlines(True),fromfile='NJR_'+stem+'.lean',tofile='NJZ_'+stem+'.lean')))
walker=subprocess.check_output(['git','show','HEAD:evidence/axaudit2-20261102/NEP_WALKER.lean'])
retained=Path('evidence/tx2-native6-20261108/NJJ_WALKER_SOURCE.lean.txt').read_bytes();assert walker==retained
E.joinpath('NJZ_WALKER_PIN.json').write_text(json.dumps(dict(byte_identical=True,sha256=hashlib.sha256(walker).hexdigest(),canonical='evidence/axaudit2-20261102/NEP_WALKER.lean',retained='evidence/tx2-native6-20261108/NJJ_WALKER_SOURCE.lean.txt'),indent=2)+'\n')
print(f'Audit preflight PASS: {len(mods)} own modules, {len(roots)} roots, byte-identical hardened walker.')
