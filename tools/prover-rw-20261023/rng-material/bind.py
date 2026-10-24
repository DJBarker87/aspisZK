"""Bind actual LLBC declarations to unchanged source and capped input receipts."""
from pathlib import Path
import json,hashlib,sys
D=Path(__file__).resolve().parent;R=D.parents[2]
E=R/'docs/research/100bit-spend-path-20261013/evidence/prover-rw-20261023/rng-material'
sha=lambda b:hashlib.sha256(b).hexdigest()
p=D/'ProverRwRngMaterialBody.llbc';d=json.loads(p.read_text())['translated']
receipt=json.loads((E/('rng-material-extract-'+sys.argv[1])/'receipt.json').read_text())
files=[];source_texts={};mismatches=[]
for f in d['files']:
 local=f['name'].get('Local')
 if not local or not (R/local).is_file():continue
 b=(R/local).read_bytes();expected=receipt['source_sha256'].get(local)
 if expected!=sha(b):
  archived=E.parent/'rng-native/host-state-only-prefix.rs.txt'
  assert local=='crates/aspis-core/src/state_only_prefix.rs' and sha(archived.read_bytes())==expected
  source_texts[local]=archived.read_text();mismatches.append(local)
 else:source_texts[local]=b.decode()
 if f.get('contents') is not None:assert sha(f['contents'].encode())==sha(b)
 files.append(dict(path=local,current_sha256=sha(b),host_sha256=expected,whole_file_matches=sha(b)==expected,bytes=len(b),embedded=f.get('contents') is not None))
entries=[]
for group in ['type_decls','fun_decls','trait_decls','trait_impls','global_decls']:
 for x in d[group]:
  if not x:continue
  m=x['item_meta'];sp=m['span']['data'];body=x.get('body');sp=body['Structured']['span']['data'] if isinstance(body,dict) and 'Structured' in body else sp;f=d['files'][sp['file_id']];local=f['name'].get('Local')
  if not local or not (R/local).is_file():continue
  lines=source_texts[local].splitlines(keepends=True);start,end=sp['beg'],sp['end']
  fragment=''.join(lines[start['line']-1:end['line']])
  current=(R/local).read_text();current_offset=current.find(fragment)
  assert current_offset>=0,(local,'referenced source declaration changed',sp)
  current_line=current.count('\n',0,current_offset)+1
  entries.append(dict(group=group,def_id=x.get('def_id'),qualified=m['name'],span=sp,path=local,opacity=m['opacity'],current_start_line=current_line,source_span_text=fragment,source_span_sha256=sha(fragment.encode()),signature=x.get('signature',x.get('generics')),body_or_kind_sha256=sha(json.dumps(x.get('body',x.get('kind')),sort_keys=True).encode())))
out=dict(schema='rng-material-actual-body-source-map-v1',receipt=receipt['attempt'],source_revision=receipt['source_revision'],llbc={'sha256':sha(p.read_bytes()),'bytes':p.stat().st_size},source_files=files,declarations=entries,substitutions=[],source_assessment={'whole_file_mismatches':mismatches,'assessment':'Host prefix file has only an unrelated syntax change to coordinates7,6 at line607; every referenced declaration span matches current source literally, with line offsets recorded. No whole-native identity gate. Opaque Error/Challenges remain TypeLeaves, uninstalled.'},boundary='Direct native source extraction with opaque local leaves; no owned-store or audit placeholder substitution; Aeneas/Lean status recorded separately. Not a whole-runtime refinement.')
p=D/'source-map.json';render=json.dumps(out,indent=2)+'\n'
assert len(render)<5_000_000
if '--check' in sys.argv:assert p.read_text()==render
else:p.write_text(render)
print('Bound',len(entries),'native declarations and',len(files),'source files')
