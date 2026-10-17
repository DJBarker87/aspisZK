#!/usr/bin/env python3
"""Bind actual semantic round bodies to coherent carriers and explicit arithmetic APIs."""
from pathlib import Path
import argparse,hashlib,importlib.util,json,re
R=Path(__file__).resolve().parents[5];H=Path(__file__).resolve().parent;BASE=R/'docs/research/100bit-spend-path-20261013';sha=lambda b:hashlib.sha256(b).hexdigest()
spec=importlib.util.spec_from_file_location('binder',BASE/'tools/prepared-actual-extraction-kit/bind.py');a=importlib.util.module_from_spec(spec);spec.loader.exec_module(a)
p=argparse.ArgumentParser();p.add_argument('--generated',type=Path,required=True);p.add_argument('--out',type=Path,required=True);p.add_argument('--check',action='store_true');x=p.parse_args()
prior=BASE/'lean/bridge-tx1-e5c186ba3-20261016/AspisR1PublicPreparation';raw={n:(x.generated/n).read_bytes()for n in ['Types.lean','Funs.lean']};current={n:a.chunks(raw[n])for n in raw};audit={}
for n in raw:
 old=a.chunks((prior/n).read_bytes());shared=set(old)&set(current[n]);items=[]
 for name in sorted(shared):
  text=current[n][name]
  if name=='r1_wire.Error':text=text.removeprefix('@[discriminant isize]\n')
  if name=='aspis_core.Digest32':text=text.replace('Self → (Slice (Slice Std.U8))','Self → Slice (Slice Std.U8)')
  for loop,binder in [('sampler.qm31_digits_loop0.body','rank1'),('sampler.qm31_digits_loop1.body','digits1'),('sampler.qm31_div_pass_loop.body','rank1')]:
   if name==loop:text=re.sub(r'\b'+binder+r'\b','a',text)
  assert a.a.tokens(text)==a.a.tokens(old[name]),(n,name)
  items.append({'declaration':name,'prior_token_sha256':sha(json.dumps(a.a.tokens(old[name]),separators=(",",":")).encode()),'current_token_sha256':sha(json.dumps(a.a.tokens(text),separators=(",",":")).encode()),'statement_diff':''.join(__import__('difflib').unified_diff(current[n][name].splitlines(True),text.splitlines(True),fromfile='raw-current',tofile='accepted-canonical')), 'normalization_rule':'Use accepted canonical named-instance overlay for r1_wire.Error discriminant macro; remove only redundant Digest32 parentheses; alpha-rename only preaudited sampler localbind results.'})
 audit[n]={'common_declarations':items,'prior_source_sha256':sha((prior/n).read_bytes()),'raw_current_sha256':sha(raw[n])}
newtypes=[current['Types.lean'][n]for n in current['Types.lean']if n not in a.chunks((prior/'Types.lean').read_bytes())]
helpers=[n for n in current['Funs.lean']if n not in a.chunks((prior/'Funs.lean').read_bytes())and n not in ['r1_semantic.semantic_round','r1_semantic.semantic_rounds','r1_semantic.rounds_entry']]
names=['r1_semantic.semantic_round','r1_semantic.semantic_rounds','r1_semantic.rounds_entry'];mappings={'r1_semantic.semantic_round':'RoundModel.step B','r1_semantic.semantic_rounds':'RoundModel.rounds B','r1_semantic.rounds_entry':'RoundModel.entry B','r1_wire.ValidatedRecord.decode_k':'B.decode','r1_semantic.semantic_boundary':'B.boundary','r1_semantic.semantic_value':'B.value'};defs=[];bodyaudit=[]
for name in names:
 original=current['Funs.lean'][name];pat=re.compile('|'.join(re.escape(n)+r'(?![A-Za-z0-9_.])'for n in sorted(mappings,key=len,reverse=True)));counts={n:len(re.findall(re.escape(n)+r'(?![A-Za-z0-9_.])',original))for n in mappings};text=pat.sub(lambda m:mappings[m[0]],original);target=mappings[name];assert text.startswith('def '+target+'\n');text=text.replace('def '+target+'\n','def '+target.removesuffix(' B')+' (B : RoundModel.Boundaries)\n',1);defs.append(text);bodyaudit.append({'source_declaration':name,'source_token_sha256':sha(json.dumps(a.a.tokens(original),separators=(",",":")).encode()),'adapted_sha256':sha(text.encode()),'identifier_replacement_counts':{n:c for n,c in counts.items()if c},'binder_addition':' (B : RoundModel.Boundaries)','sole_other_change':'Insert explicit Boundaries parameter after new definition name'})
text='''import AspisR1PublicPreparation.Funs
open Aeneas Aeneas.Std Result ControlFlow Error
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 2048
namespace AspisR1PublicPreparation
'''+ '\n'.join(newtypes)+'''\nstructure RoundModel.Boundaries where
  decode : (N : Usize) → r1_wire.ValidatedRecord → Usize →
    Result (core.result.Result (Array aspis_core.field.QM31 N) r1_wire.Error)
  boundary : Array aspis_core.field.QM31 28#usize → Result aspis_core.field.QM31
  value : Array aspis_core.field.QM31 28#usize → Array aspis_core.field.QM31 10#usize → Usize → Result aspis_core.field.QM31
'''+ '\n'.join(current['Funs.lean'][n]for n in helpers)+'\n'+'\n'.join(defs)+'\n#print axioms RoundModel.step\n#print axioms RoundModel.rounds\n#print axioms RoundModel.entry\nend AspisR1PublicPreparation\n'
assert not re.search(r'^\s*(axiom|opaque)\b',text,re.M)
pins={'source_revision':'a555c8526','rule':'All shared canonical carriers/functions token-identical after recorded parentheses/alpha naming normalizations. Entire round/entry bodies bound only by listed identifier substitutions+explicit parameter. New extracted QM31 equality functions retained exactly. No external template imported.','common_carrier_audit':audit,'added_helper_declarations':helpers,'added_type_declarations':len(newtypes),'model_body_audits':bodyaudit,'raw_funs_sha256':sha(raw['Funs.lean']),'identifier_map':mappings,'output_sha256':sha(text.encode())}
pins['carrier_inventory']={file:{'raw_current_sha256':inventory['raw_current_sha256'],'common_unchanged':[{'declaration':q['declaration'],'old_token_sha256':q['prior_token_sha256'],'current_token_sha256':q['current_token_sha256']}for q in inventory['common_declarations']],'explicit_statement_normalizations':{q['declaration']:{'statement_diff':q['statement_diff'],'rule':q['normalization_rule']}for q in inventory['common_declarations']if q['statement_diff']}}for file,inventory in audit.items()}
outputs={'ExtractedSemanticRoundsModel.lean':text.encode(),'binding-pins.json':(json.dumps(pins,indent=2)+'\n').encode()}
for n,b in outputs.items():
 q=x.out/n
 if x.check:assert q.read_bytes()==b,n
 else:q.parent.mkdir(parents=True,exist_ok=True);q.write_bytes(b)
print(json.dumps({'status':'PASS','model_sha256':sha(text.encode()),'checked':x.check}))
