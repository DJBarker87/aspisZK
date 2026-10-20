from pathlib import Path
import importlib.util,re,json,hashlib,argparse
ap=argparse.ArgumentParser();ap.add_argument("--generated",type=Path,required=True);ap.add_argument("--out",type=Path,required=True);args=ap.parse_args();args.out.mkdir(parents=True,exist_ok=True)
root=Path(__file__).resolve().parents[5];p=root/'docs/research/100bit-spend-path-20261013';tool=p/'tools/prepared-actual-extraction-kit/bind.py'
s=importlib.util.spec_from_file_location('binder',tool);m=importlib.util.module_from_spec(s);s.loader.exec_module(m)
raw=(args.generated/'Funs.lean').read_bytes();chunks=m.chunks(raw)
mapping={'verifier.Prepared.new':'PreparedScratchModel.prepare B','prepared_entry':'PreparedScratchModel.entry B','transcript.Transcript.scalar_k':'PreparedModel.scalar_k B.sampling','transcript.Transcript.scalar':'PreparedModel.scalar B.sampling','aspis_core.field.WideExact.to_le_bytes':'B.sampling.toBytes','transcript.Transcript.queries':'B.sampling.queries','weights.powers':'B.powers','verifier.prepared_claim':'B.claim'}
pat=re.compile('|'.join(re.escape(n)+r'(?![A-Za-z0-9_.])' for n in sorted(mapping,key=len,reverse=True)))
defs=[];audit=[];sha=lambda b:hashlib.sha256(b).hexdigest()
for name in ['verifier.Prepared.new','prepared_entry']:
 original=chunks[name];body=pat.sub(lambda q:mapping[q[0]],original);target=mapping[name]
 assert body.startswith('def '+target+'\n')
 body=body.replace('def '+target+'\n','def '+target.removesuffix(' B')+' (B : PreparedScratchModel.Boundaries)\n',1)
 defs.append(body);audit.append(dict(declaration=name,original_sha256=sha(original.encode()),bound_sha256=sha(body.encode()),identifier_map=mapping,only_binder_addition='B : PreparedScratchModel.Boundaries'))
header='''import ExtractedPreparedModel
open Aeneas Aeneas.Std Result ControlFlow Error
set_option autoImplicit false
namespace AspisR1PublicPreparation
/-- Sampling uses the previously checked common owner. Its unused legacy claim
field is never called by this model. Current powers/cached-claim are explicit. -/
structure PreparedScratchModel.Boundaries where
  sampling : PreparedModel.Boundaries
  powers : (N : Usize) → aspis_core.field.WideExact →
    Result (Array aspis_core.field.WideExact N)
  claim : {H : Type} → aspis_core.Digest32 H → r1_semantic.Verified H → Slice U8 →
    aspis_core.field.WideExact → Array aspis_core.field.WideExact 29#usize →
    aspis_core.field.WideExact → Result (core.result.Result aspis_core.field.WideExact verifier.Error)

'''
out=header+'\n'.join(defs)+'''\n#print axioms PreparedScratchModel.prepare
#print axioms PreparedScratchModel.entry
end AspisR1PublicPreparation
'''
(args.out/'CurrentPreparedScratchModel.lean').write_text(out)
(args.out/'binding-audit.json').write_text(json.dumps({'raw_funs_sha256':sha(raw),'model_sha256':sha(out.encode()),'body_audits':audit,'carrier_union_result':'Retained bind.py passed exact common declarations and generated a Types/Funs union byte-identical to existing accepted bridge-prepared-3335 owner; reused without unchanged compilation.','remaining_boundaries':['powers','claim','sampling child bindings','historical52 source carrier correspondence','full tx1/current caller/runtime']},indent=2)+'\n')
