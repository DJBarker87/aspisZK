#!/usr/bin/env python3
"""Coherent canonical carrier union; exact whole-body explicit-boundary binder."""
from pathlib import Path
import argparse,hashlib,importlib.util,json,re
ROOT=Path(__file__).resolve().parents[5];BASE=ROOT/'docs/research/100bit-spend-path-20261013';HERE=Path(__file__).resolve().parent
sha=lambda b:hashlib.sha256(b).hexdigest()
spec=importlib.util.spec_from_file_location('audit',BASE/'tools/public-binding-followup-kit/bridge-callers.py');a=importlib.util.module_from_spec(spec);spec.loader.exec_module(a)
def chunks(raw):
 text=a.uncomment(raw.decode());pattern=re.compile(r'^\s*(?:@\[[^\]]*\]\s*)*(?:def|structure|inductive|abbrev|instance)\s+(\S+)',re.M);matches=list(pattern.finditer(text));out={}
 for i,m in enumerate(matches):
  end=matches[i+1].start() if i+1<len(matches) else text.rfind('\nend ')
  out[m[1]]=re.sub(r'\s*@\[[^\]]*\]\s*$','',text[m.start():end]).strip()+'\n'
 return out

def main():
 p=argparse.ArgumentParser();p.add_argument('--generated',type=Path,required=True);p.add_argument('--out',type=Path,required=True);p.add_argument('--check',action='store_true');x=p.parse_args()
 olddir=BASE/'lean/bridge-public-callers-c16-20261016/AspisR1PublicPreparation';raws={n:(x.generated/n).read_bytes() for n in ['Types.lean','Funs.lean']};prior={n:(olddir/n).read_bytes() for n in raws};inventory={};outputs={}
 modelnames=['transcript.Transcript.scalar','transcript.Transcript.scalar_k','verifier.Prepared.new','prepared_entry']
 for file in raws:
  old=chunks(prior[file]);new=chunks(raws[file]);normalizations={}
  if file=='Types.lean':
   name='aspis_core.Digest32';before=new[name];after=before.replace('Self → (Slice (Slice Std.U8))','Self → Slice (Slice Std.U8)');assert before!=after;new[name]=after;normalizations[name]={'raw_statement':before,'canonical_statement':after,'rule':'Remove only redundant parentheses around the Slice argument type; retained canonical carrier declaration has definitionally identical field type.'}
  if file=='Funs.lean':
   for name,binder in [('sampler.qm31_digits_loop0.body','rank1'),('sampler.qm31_digits_loop1.body','digits1'),('sampler.qm31_div_pass_loop.body','rank1')]:
    before=new[name];pattern=re.compile(r'\b'+binder+r'\b');assert len(pattern.findall(before))==2;after=pattern.sub('a',before);new[name]=after;normalizations[name]={'raw_statement':before,'canonical_statement':after,'rule':'Alpha-rename only the local Array.update bind result and its sole return occurrence; no free identifier changes.'}
  shared=sorted(set(old)&set(new));entries=[]
  for name in shared:
   assert a.tokens(old[name])==a.tokens(new[name]),(file,name,'changed common declaration')
   entries.append({'declaration':name,'old_token_sha256':sha(json.dumps(a.tokens(old[name]),separators=(',',':')).encode()),'current_token_sha256':sha(json.dumps(a.tokens(new[name]),separators=(',',':')).encode()),'statement_diff':''})
  additions=[n for n in new if n not in old and n not in modelnames]
  text=prior[file].decode();at=text.rfind('\nend AspisR1PublicPreparation');assert at>=0
  text=text[:at]+'\n\n/-! Exact newly emitted declarations; original canonical declarations retained. -/\n'+ '\n'.join(new[n] for n in additions)+text[at:]
  outputs['AspisR1PublicPreparation/'+file]=text.encode();inventory[file]={'prior_sha256':sha(prior[file]),'raw_current_sha256':sha(raws[file]),'common_unchanged':entries,'new_declarations':additions,'all_original_declarations_retained':len(old),'explicit_statement_parenthesization_normalizations':normalizations}
 new=chunks(raws['Funs.lean'])
 boundary='''structure PreparedModel.Boundaries where
  toBytes : aspis_core.field.WideExact → Result (Array U8 32#usize)
  fromQm : aspis_core.field.QM31 → Result aspis_core.field.WideExact
  ordinary : (Array U8 32#usize) → Result aspis_core.field.WideExact
  gamma : (Array U8 32#usize) → Result aspis_core.field.WideExact
  queries : {H : Type} → aspis_core.Digest32 H → transcript.Transcript H → U8 → Slice U8 →
    Result (core.result.Result (Array U32 22#usize) verifier.Error × transcript.Transcript H)
  claim : {H : Type} → aspis_core.Digest32 H → r1_semantic.Verified H → Slice U8 →
    aspis_core.field.WideExact → aspis_core.field.WideExact → aspis_core.field.WideExact →
    Result (core.result.Result aspis_core.field.WideExact verifier.Error)
'''
 mappings={'transcript.Transcript.scalar_k':'PreparedModel.scalar_k B','transcript.Transcript.scalar':'PreparedModel.scalar B','verifier.Prepared.new':'PreparedModel.prepare B','prepared_entry':'PreparedModel.entry B','aspis_core.field.WideExact.to_le_bytes':'B.toBytes','aspis_core.field.WideExact.from_qm31':'B.fromQm','sampler.ordinary_sample':'B.ordinary','sampler.gamma_sample':'B.gamma','transcript.Transcript.queries':'B.queries','verifier.prepared_claim':'B.claim'}
 defs=[];audits=[]
 for name in modelnames:
  body=new[name];original=body
  # Simultaneous exact identifier replacements: scalar cannot rewrite scalar_k.
  pat=re.compile('|'.join(re.escape(n)+r'(?![A-Za-z0-9_.])' for n in sorted(mappings,key=len,reverse=True)))
  counts={n:len(re.findall(re.escape(n)+r'(?![A-Za-z0-9_.])',body)) for n in mappings};body=pat.sub(lambda m:mappings[m[0]],body)
  target=mappings[name];assert body.startswith('def '+target+'\n');body=body.replace('def '+target+'\n','def '+target.removesuffix(' B')+' (B : PreparedModel.Boundaries)\n',1)
  defs.append(body);audits.append({'source_declaration':name,'source_token_sha256':sha(json.dumps(a.tokens(original),separators=(',',':')).encode()),'adapted_sha256':sha(body.encode()),'identifier_replacement_counts':{n:v for n,v in counts.items() if v},'sole_binder_addition':'(B : PreparedModel.Boundaries) after declaration name; unchanged other statement/body tokens.'})
 model='''import AspisR1PublicPreparation.Funs
open Aeneas Aeneas.Std Result ControlFlow Error
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 2048
namespace AspisR1PublicPreparation
'''+boundary+'\n'+'\n'.join(defs)+'\n#print axioms PreparedModel.scalar\n#print axioms PreparedModel.scalar_k\n#print axioms PreparedModel.prepare\n#print axioms PreparedModel.entry\nend AspisR1PublicPreparation\n'
 assert not re.search(r'^\s*(axiom|opaque)\b',model,re.M)
 outputs['ExtractedPreparedModel.lean']=model.encode();pins={'source_revision':'3335eecf2f2a08096abe95c67ac6b304f2df6284','rule':'Common declarations compare exact comment-free token streams including attrs and string bytes; retain all canonical original declarations, append newly emitted declarations. Six external template signatures become explicit structure fields. Model bodies use only listed simultaneous identifier substitutions and one explicit Boundaries binder. No global opaque/axiom imported.','carrier_inventory':inventory,'model_body_audits':audits,'identifier_map':mappings,'output_hashes':{n:sha(b) for n,b in outputs.items()}}
 outputs['binding-pins.json']=(json.dumps(pins,indent=2)+'\n').encode()
 for name,b in outputs.items():
  p=x.out/name
  if x.check:assert p.read_bytes()==b,name
  else:p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(b)
 print(json.dumps({'status':'PASS','checked':x.check,'types_sha256':sha(outputs['AspisR1PublicPreparation/Types.lean']),'funs_sha256':sha(outputs['AspisR1PublicPreparation/Funs.lean']),'model_sha256':sha(outputs['ExtractedPreparedModel.lean'])}))
if __name__=='__main__':main()
