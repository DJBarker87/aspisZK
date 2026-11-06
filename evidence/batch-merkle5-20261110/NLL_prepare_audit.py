"""Freeze current successful new modules; preserve source-backed expected headers."""
from pathlib import Path
import json,re,hashlib,subprocess,lzma
E=Path(__file__).resolve().parent
selected={}
for line in (E/'NLL_ATTEMPTS.jsonl').read_text().splitlines():
 a=json.loads(line)
 if a['kind']!='lean' or a['exit_status']!=0:continue
 r=json.loads((E/a['full_receipt']).read_text());m=r['module']
 if m in ['NLL_Driver','NLL_ProofDriver','NLL_COMBINED_IMPORT']:continue
 if not all((E/n).is_file() and hashlib.sha256((E/n).read_bytes()).hexdigest()==h for n,h in r['source_hashes'].items()):continue
 selected[m]=r
current={p.stem for p in E.glob('NLL_*.lean') if p.stem not in ['NLL_Driver','NLL_ProofDriver','NLL_COMBINED_IMPORT']}
assert current==set(selected),(sorted(current-set(selected)),sorted(set(selected)-current))
roots={'AspisR1.RPx_Deployed.deployed'}
for r in selected.values():
 for line in r['print_axioms']:
  hit=re.fullmatch(r"'([^']+)' depends on axioms: \[([^]]*)\]",line)
  empty=re.fullmatch(r"'([^']+)' does not depend on any axioms",line)
  if empty:roots.add(empty[1]);continue
  assert hit,line
  assert {x.strip() for x in hit[2].split(',') if x.strip()}<={'propext','Classical.choice','Quot.sound'},line
  roots.add(hit[1])
# All retained NKV support roots re-audited in this current combined environment.
roots.update(json.loads(Path('evidence/batch-merkle4-20261109/NKV_AUDIT_ROOTS.json').read_text())['roots'])
modules=['NLG_COMBINED_IMPORT','NKV_COMBINED_IMPORT']+sorted(selected)
public_defs=['NLL.Frame','NLL.Event','NLL.Terminal','NLL.Loop','NLL.Invocation','NLL.Pending','NLL.AbortLoop','NLL.AbortInvocation','NLL_Parent.Calls','NLL_Parent.AbortCalls','NLL_BatchSource.Invocation','NLL_BatchAbort.Invocation']
(E/'NLL_COMBINED_IMPORT.lean').write_text(''.join('import '+m+'\n' for m in modules)+'set_option pp.proofs false\nset_option pp.all true\n'+''.join('#print '+n+'\n' for n in public_defs)+''.join('#print '+r+'\n#print axioms '+r+'\n' for r in sorted(roots)))
records={}
for filename in ['evidence/batch-merkle4-20261109/NKV_EXPECTED_IMPORTS.jsonl','evidence/ledger21-20261110/NLG_EXPECTED_IMPORTS.jsonl']:
 p=Path(filename)
 if p.is_file():data=p.read_bytes()
 elif Path(filename+'.xz').is_file():data=lzma.decompress(Path(filename+'.xz').read_bytes())
 else:data=subprocess.check_output(['git','show','HEAD:'+filename])
 # Preserve logical input once in this evidence directory when not materialized.
 if not p.is_file():
  pin=E/('NLL_'+p.stem+'.jsonl.xz');pin.write_bytes(lzma.compress(data,preset=6));pin.with_suffix(pin.suffix+'.sha256').write_text(hashlib.sha256(data).hexdigest()+'\n')
 for line in data.decode().splitlines():
  row=json.loads(line);m=row['module']
  assert m not in records or records[m]==row,m
  records[m]=row
# Source-backed headers for newly reached retained NKE support modules.
header_pins={}
for filename in subprocess.check_output(['git','ls-files','evidence/tx2-native9-20261108'],text=True).splitlines():
 p=Path(filename)
 if p.suffix!='.lean' or len(p.parts)!=3:continue
 data=subprocess.check_output(['git','show','HEAD:'+filename])
 m=p.stem
 row={'module':m,'imports':list(dict.fromkeys(['Init']+re.findall(r'^import (?:all )?([A-Za-z0-9_.]+)',data.decode(),re.M)))}
 assert m not in records or records[m]==row,m
 records[m]=row
 header_pins[m]={'source':filename,'sha256':hashlib.sha256(data).hexdigest(),'imports':row['imports']}
(E/'NLL_NKE_SOURCE_HEADERS.json').write_text(json.dumps(header_pins,indent=2)+'\n')
for m,r in selected.items():
 src=next(n for n in r['sources'] if n.endswith('.lean'))
 records[m]={'module':m,'imports':list(dict.fromkeys(['Init']+re.findall(r'^import (?:all )?([A-Za-z0-9_.]+)',(E/src).read_text(),re.M)))}
records['NLL_COMBINED_IMPORT']={'module':'NLL_COMBINED_IMPORT','imports':['Init']+modules}
(E/'NLL_EXPECTED_IMPORTS.jsonl').write_text(''.join(json.dumps(records[m])+'\n' for m in sorted(records)))
(E/'NLL_AUDIT_ROOTS.json').write_text(json.dumps({'roots':sorted(roots),'groups':[sorted(roots)]},indent=2)+'\n')
(E/'NLL_AUDIT_MODULES.json').write_text(json.dumps([['NLL_COMBINED_IMPORT']])+'\n')
(E/'NLL_PROOF_SET.json').write_text(json.dumps({m:{'attempt':r['attempt'],'source_hashes':r['source_hashes'],'source_revision':r['source_revision'],'print_axioms':r['print_axioms']} for m,r in selected.items()},indent=2)+'\n')
print(json.dumps({'new_modules':len(selected),'roots':len(roots),'expected_modules':len(records)}))
