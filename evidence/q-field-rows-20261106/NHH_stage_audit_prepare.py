from pathlib import Path
import json,re,difflib,sys
E=Path(__file__).resolve().parent;P=E.parent;stage=sys.argv[1]
modules=['Embedding','BaseOps','ScalarDomain','EncodedScalar','CMInverse','CMTrace','CMSampler','CMAlgebra','CMBridge','AllScalar','CMAll']
if stage=='q':modules+=['QInverse','QAll','QTrace','QBridge','QNeg','StubDomains','InverseOutcomes']
roots=['NHH_'+m+'.'+name for m in modules for name in re.findall(r'^theorem (\w+)',(E/('NHH_'+m+'.lean')).read_text(),re.M)]+['AspisR1.RPx_Deployed.deployed']
(E/'NHH_AUDIT_ROOTS.json').write_text(json.dumps(dict(roots=roots,stage=stage,group_size=10),indent=1)+'\n')
(E/'NHH_COMBINED_IMPORT.lean').write_text('import NGK_COMBINED_IMPORT\n'+''.join('import NHH_'+m+'\n'for m in modules)+'#print axioms AspisR1.RPx_Deployed.deployed\n')
orig=(P/'slice-d-field3-20261105/NGH_Driver.lean').read_text();s=orig;a=s.index('    else if mode == "scan"');b=s.index('    else (#[], #[])',a)
block='    else if mode == "scan" then (#[`NHH_COMBINED_IMPORT], #[])\n'
for i in range((len(roots)+9)//10):block+=f'    else if mode == "proof{i}" then\n      (#[`NHH_COMBINED_IMPORT], #['+', '.join('`'+r for r in roots[10*i:10*i+10])+'])\n'
s=s[:a]+block+s[b:];s=s.replace('NGH_EXPECTED_IMPORTS','NHH_EXPECTED_IMPORTS').replace('NGH_LOADED_scan','NHH_LOADED_scan')
(E/'NHH_Driver.lean').write_text(s);(E/f'NHH_DRIVER_{stage}.diff').write_text(''.join(difflib.unified_diff(orig.splitlines(True),s.splitlines(True),fromfile='NGH_Driver.lean',tofile='NHH_Driver.lean')))
expected={}
for p in [P/'pool-retarget-20261105/NGK_EXPECTED_IMPORTS.jsonl',P/'slice-d-field3-20261105/NGH_EXPECTED_IMPORTS.jsonl',P/'slice-q-accum-20261104/NFS_EXPECTED_IMPORTS.jsonl']:
 for l in p.read_text().splitlines():x=json.loads(l);expected.setdefault(x['module'],x)
for m in ['NHH_'+n for n in modules]+['NHH_COMBINED_IMPORT']:
 imports=['Init']+[n for l in (E/(m+'.lean')).read_text().splitlines() if l.startswith('import ') for n in l[7:].split()]
 expected[m]=dict(module=m,imports=list(dict.fromkeys(imports)))
(E/'NHH_EXPECTED_IMPORTS.jsonl').write_text(''.join(json.dumps(x)+'\n' for _,x in sorted(expected.items())))
s=(P/'slice-d-field3-20261105/NGH_review_batch.py').read_text().replace('NGH_','NHH_').replace("out=B/'NHH_review_resume'", "out=B/os.environ.get('NHH_REVIEW_OUTPUT','NHH_review')").replace('(len(roots)+4)//5','(len(roots)+9)//10')
(E/'NHH_review_batch.py').write_text(s)
print(json.dumps(dict(stage=stage,roots=len(roots),modules=len(modules))))
