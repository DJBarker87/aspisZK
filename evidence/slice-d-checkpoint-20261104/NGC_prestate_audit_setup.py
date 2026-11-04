from pathlib import Path
import json,hashlib
E=Path('evidence/slice-d-checkpoint-20261104');p=E/'NGC_COMBINED_IMPORT.lean';s=p.read_text().replace('import NGC_InitialInvariant\n','import NGC_InitialInvariant\nimport NGC_PrestateBridge\n')+'#print axioms AspisR1.NGC_PrestateBridge.from_initializers\n';p.write_text(s)
p=E/'NGC_EXPECTED_IMPORTS.jsonl';rows={r['module']:r for r in map(json.loads,p.read_text().splitlines())}
for n in ['NGC_COMBINED_IMPORT','NGC_PrestateBridge']:
 text=(E/(n+'.lean')).read_text();rows[n]=dict(module=n,imports=list(dict.fromkeys(['Init']+[m for l in text.splitlines()if l.startswith('import ')for m in l.split()[1:]])))
p.write_text(''.join(json.dumps(r)+'\n'for r in rows.values()))
s=(E/'NGC_Driver.lean').read_text().replace('if mode == "fixtures" then','if mode.startsWith "fixtures" then').replace('if mode == "scan" || mode == "queryscan" then','if mode.startsWith "scan" || mode == "queryscan" then')
a=s.index('    else\n      (#[`NGC_COMBINED_IMPORT]');b=s.index('\n  let env',a);s=s[:a]+'    else\n      (#[`NGC_COMBINED_IMPORT],#[`AspisR1.NGC_PrestateBridge.from_initializers,`AspisR1.RPx_Deployed.deployed])'+s[b:];(E/'NGC_FinalDriver.lean').write_text(s)
s=(E/'NGC_final_audit_batch.py').read_text().replace('NGC_ProofDriver','NGC_FinalDriver');a=s.index("modes=['fixtures'");b=s.index('\nfor mode in modes:',a);s=s[:a]+"modes=['fixturesFinal','prestate','scanFinal']"+s[b:];s=s.replace("if mode=='fixtures':", "if mode=='fixturesFinal':").replace("results'+os.environ.get('NGC_AUDIT_PART','1')", "results'+'3'");(E/'NGC_prestate_audit_batch.py').write_text(s)
p=E/'NGC_run.py';s=p.read_text().replace("'NGC_ProofDriver','NGC_Stage2Driver'", "'NGC_ProofDriver','NGC_Stage2Driver','NGC_FinalDriver'")
marker="elif kind=='auditbatch' and target=='NGC_Stage2Driver':"
extra="""elif kind=='auditbatch' and target=='NGC_FinalDriver':
 files['NGC_prestate_audit_batch.py']=(E/'NGC_prestate_audit_batch.py').read_text()
 files['NGC_EXPECTED_IMPORTS.jsonl']=(E/'NGC_EXPECTED_IMPORTS.jsonl').read_text()
 sources=['NGC_generated/NGC_FinalDriver.lean','NGC_prestate_audit_batch.py','NGC_native/NGC_FinalDriver.c','NGC_native/NGC_WALKER.c','NGC_native/NGC_MemoryLimit.c']
 command=['python3','NGC_prestate_audit_batch.py']
"""
s=s.replace(marker,extra+marker);p.write_text(s)
