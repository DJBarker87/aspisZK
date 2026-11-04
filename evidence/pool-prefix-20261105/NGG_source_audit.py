"""Additional source erasure checks; never promotes partial native evidence."""
from pathlib import Path
import json,subprocess,hashlib,re
E=Path(__file__).resolve().parent;REV='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387'
read=lambda p:subprocess.check_output(['git','show',REV+':'+p],text=True)
canon=lambda s:re.sub(r'\s+','',s)
src=read('programs/aspis-pool/src/pair_forest.rs')
a=src.index('    let (request_bytes, hints) =',src.index('pub(crate) fn process_pair_forest_terminal_with_verifier_v1'));z=src.index('    let master = decode_terminal_master_box_v1',a)
expected=src[a:z].replace('decode_terminal_request_box_v1(request_bytes)','decode(request_bytes)')
positives=[];controls=[]
for p in sorted(E.glob('NGG_K*-shape.json')):
 d=json.loads(p.read_text())
 if d.get('kind')!='decode-cut':continue
 s=d['source'];a=s.index('    let (request_bytes, hints) =');b=s.index('Ok((request,master_account',a);body=s[a:b]
 good=canon(body)==canon(expected)
 if d['mode']=='argument':assert not good;controls.append(p.stem)
 else:assert good,p;positives.append(p.stem)
# Matched independent mutations of each of the five caller argument/control lines.
mutations=[]
for text,replacement in [('split_pair_forest_terminal_bump_hints_v1(instruction_data)','split_pair_forest_terminal_bump_hints_v1(&instruction_data[1..])'),('decode(request_bytes)','decode(&request_bytes[1..])'),('accounts.first()','accounts.last()'),('accounts.get(1)','accounts.get(0)'),('accounts.get(2)','accounts.get(1)')]:
 assert text in expected
 wrong=expected.replace(text,replacement,1)
 assert canon(wrong)!=canon(expected)
 mutations.append({'source_fragment_sha256':hashlib.sha256(text.encode()).hexdigest(),'rejected':True})
# No runtime assumption proposed in prose appears in a formal theorem.
formal=[p for p in E.rglob('*.lean') if 'NGG_imports' not in p.parts]
for p in formal:
 if p.name=='NGG_CLAIM_AUDIT.lean':
  assert 'env.contains name' in p.read_text() and not re.search(r'^\s*(?:theorem|axiom)\s',p.read_text(),re.M)
  continue
 assert 'RuntimeCpiReadonlyEntry7' not in p.read_text(),p
out={'revision':REV,'frozen_prefix_sha256':hashlib.sha256(src[src.index('    let (request_bytes, hints) =',src.index('pub(crate) fn process_pair_forest_terminal_with_verifier_v1')):z].encode()).hexdigest(),'native_cut_erasure':positives,'argument_controls':controls,'source_mutations':mutations,'runtime_cpi_proposal_used':False,'classification':'source check only; full modifies/domain/native production association OPEN'}
(E/'NGG_SOURCE_AUDIT.json').write_text(json.dumps(out,indent=1)+'\n')
print(json.dumps({'source_cuts_checked':len(positives),'argument_controls':len(controls),'native_composed_credit':False}))
