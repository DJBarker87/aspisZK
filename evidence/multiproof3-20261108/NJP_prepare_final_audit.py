from pathlib import Path
import json,re,hashlib
E=Path(__file__).resolve().parent
attempts=[json.loads(x) for x in (E/'NJP_ATTEMPTS.jsonl').read_text().splitlines()]
last={x['module']:x for x in attempts if x['kind']=='lean'}
modules=[];roots=['AspisR1.RPx_Deployed.deployed'];pins={}
for p in sorted((E/'NJP_lean').glob('NJP_*.lean')):
 m=p.stem
 if m in ['NJP_COMBINED_IMPORT','NJP_Driver','NJP_ProofDriver']:continue
 a=last.get(m)
 if not a or a['exit_status']!=0:continue
 s=p.read_text(); matches=re.findall(r'^#print axioms (\S+)',s,re.M)
 if not matches:continue
 modules.append(m)
 namespace=re.findall(r'^namespace (\S+)',s,re.M)[0]
 for n in matches:roots.append(n if n.startswith(namespace+'.') else namespace+'.'+n)
 pins[m]={'source_sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'successful_attempt':a['attempt']}
imports=['NJK_COMBINED_IMPORT','NJE_COMBINED_IMPORT']+modules
s=''.join('import '+m+'\n' for m in imports)+'\n#check AspisR1.RPx_Deployed.deployed\n#print axioms AspisR1.RPx_Deployed.deployed\n#print NJP_PermutationPacket.TX1_306\n#print NJP_CompressionPacket.TX1_305\n'
for p in [E/'NJP_COMBINED_IMPORT.lean',E/'NJP_lean/NJP_COMBINED_IMPORT.lean']:p.write_text(s)
expected={d['module']:d['imports'] for d in map(json.loads,(E/'NJP_GATE1_EXPECTED_IMPORTS.jsonl').read_text().splitlines())}
for m in modules:
 s=(E/'NJP_lean'/f'{m}.lean').read_text()
 expected[m]=['Init']+re.findall(r'^import (\S+)',s,re.M)
expected['NJP_COMBINED_IMPORT']=['Init']+imports
(E/'NJP_EXPECTED_IMPORTS.jsonl').write_text(''.join(json.dumps({'module':m,'imports':im})+'\n' for m,im in sorted(expected.items())))
(E/'NJP_AUDIT_ROOTS.json').write_text(json.dumps({'roots':roots,'groups':[roots]},indent=2)+'\n')
(E/'NJP_AUDIT_MODULES.json').write_text(json.dumps([['NJP_COMBINED_IMPORT']],indent=2)+'\n')
(E/'NJP_FINAL_PROOF_INVENTORY.json').write_text(json.dumps({'modules':pins,'roots':roots,'uncompiled':['NJP_VerifierView','NJP_ABIInspect'],'target_established':False},indent=2)+'\n')
for old,new in [('025','078'),('026','079'),('027','080')]:
 c=json.loads((E/f'NJP_L{old}.json').read_text());c['attempt']='NJP_L'+new;c['expected_time']='Second/final combined audit after new local row/height/native-step source proofs; reuse pinned coherent dependencies and optimized audit executables';(E/f'NJP_L{new}.json').write_text(json.dumps(c,indent=2)+'\n')
print(f'Final audit prepared: {len(modules)} modules, {len(roots)} roots; two candidate rows, verifier rows OPEN')
