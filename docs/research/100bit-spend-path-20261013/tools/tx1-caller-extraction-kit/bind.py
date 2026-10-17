#!/usr/bin/env python3
"""Bind exact emitted tx1/accumulator/mark bodies to explicit boundaries."""
from pathlib import Path
import argparse,hashlib,importlib.util,json,re
R=Path(__file__).resolve().parents[5];H=Path(__file__).resolve().parent;sha=lambda b:hashlib.sha256(b).hexdigest()
spec=importlib.util.spec_from_file_location('union',H/'union.py')
# Reuse only the small comment/token/chunk helpers without running union CLI.
s={};code=(H/'union.py').read_text().split('p=argparse.ArgumentParser()',1)[0];s['__file__']=str(H/'union.py');exec(code,s)
chunks=s['chunks'];tokens=s['a'].tokens
p=argparse.ArgumentParser();p.add_argument('--generated',type=Path,required=True);p.add_argument('--out',type=Path,required=True);a=p.parse_args();raw=(a.generated/'Funs.lean').read_bytes();new=chunks(raw)
selected=['aspis_core.field.QM31.ONE','aspis_core.field.QM31.Insts.CoreCloneClone.clone','aspis_core.field.QM31.Insts.CoreCloneClone','aspis_core.field.QM31.Insts.CoreMarkerCopy','transport.Variant.final_len','verifier.Accumulator.new.closure.Insts.CoreOpsFunctionFnOnceTupleErrorError.call_once','verifier.Accumulator.new.closure.Insts.CoreOpsFunctionFnOnceTupleErrorError','verifier.Accumulator.new','verifier.mark','verifier.tx1.closure.Insts.CoreOpsFunctionFnOnceTupleErrorError.call_once','verifier.tx1.closure.Insts.CoreOpsFunctionFnOnceTupleErrorError','verifier.tx1']
mapping={n:'Tx1Model.'+t for n,t in zip(selected,['one','cloneQm','cloneInst','copyInst','final_len','allocationError','allocationErrorClosure','newAccumulator B','mark','semanticError','semanticErrorClosure','tx1 B P'])}
mapping.update({'aspis_core.r0.heap.filled':'B.filled','r1_semantic.verify_observed':'B.verify','verifier.Prepared.new':'PreparedModel.prepare P','weights.powers':'B.powers','verifier.View.parse':'B.view','verifier.tx1_finish':'B.finish'})
header='''import ExtractedPreparedModel
open Aeneas Aeneas.Std Result ControlFlow Error
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 2048
namespace AspisR1PublicPreparation
structure Tx1Model.Boundaries where
  filled : core.marker.Copy aspis_core.field.QM31 → Usize → aspis_core.field.QM31 →
    Result (core.result.Result (alloc.vec.Vec aspis_core.field.QM31) aspis_core.r0.Error)
  verify : {H : Type} → aspis_core.Digest32 H → pool_v1.pair_forest_semantic_terminal.r0.Public →
    Slice U8 → H → Option (verifier.Phase → Result Unit) →
    Result (core.result.Result (r1_semantic.Verified H) r1_wire.Error)
  powers : (N : Usize) → aspis_core.field.WideExact → Result (Array aspis_core.field.WideExact N)
  view : Slice U8 → Result (core.result.Result verifier.View verifier.Error)
  finish : {H : Type} → aspis_core.Digest32 H → verifier.View → verifier.Prepared →
    verifier.Accumulator → Array aspis_core.field.WideExact 29#usize → Slice U8 → Slice U8 →
    Usize → H → Option (verifier.Phase → Result Unit) →
    Result (core.result.Result (alloc.vec.Vec U8) verifier.Error)
'''
pat=re.compile('|'.join(re.escape(n)+r'(?![A-Za-z0-9_.])' for n in sorted(mapping,key=len,reverse=True)));defs=[];audits=[]
for n in selected:
 source=new[n];body=pat.sub(lambda m:mapping[m[0]],source);target=mapping[n];extra=''
 if n=='verifier.Accumulator.new':extra=' (B : Tx1Model.Boundaries)'
 if n=='verifier.tx1':extra=' (B : Tx1Model.Boundaries) (P : PreparedModel.Boundaries)'
 if extra:
  head='def '+target+'\n';assert head in body,(n,body[:120]);body=body.replace(head,'def '+target.split(' ')[0]+extra+'\n',1)
 defs.append(body);audits.append({'declaration':n,'source_token_sha256':sha(json.dumps(tokens(source),separators=(',',':')).encode()),'model_sha256':sha(body.encode()),'substitutions':{k:len(re.findall(re.escape(k)+r'(?![A-Za-z0-9_.])',source)) for k in mapping if re.search(re.escape(k)+r'(?![A-Za-z0-9_.])',source)},'binder_addition':extra})
model=header+'\n'+'\n'.join(defs)+'\n'+ '\n'.join('#print axioms '+mapping[n].split(' ')[0] for n in selected)+'\nend AspisR1PublicPreparation\n';assert 'fail panic' not in model and not re.search(r'^\s*(axiom|opaque)\b',model,re.M)
a.out.mkdir(parents=True,exist_ok=True);(a.out/'ExtractedTx1Model.lean').write_text(model);record={'source_revision':'e5c186ba3bcbbf9a0cc5878077aa8848853a65cc','raw_funs_sha256':sha(raw),'model_sha256':sha(model.encode()),'exact_body_audits':audits,'identifier_map':mapping,'scope':'Complete actual tx1, actual Accumulator constructor/ONE/final_len/clone/error mapping and actual verifier observer dispatch. Five explicit function boundaries plus six PreparedModel boundaries; no source staging panic or external global imported. Actual verify_observed→public_transcript reachability and tx1_finish query/checkpoint refinement remain OPEN.'};(a.out/'tx1-binding-pins.json').write_text(json.dumps(record,indent=2,sort_keys=True)+'\n');print(json.dumps({'model_sha256':record['model_sha256'],'declarations':len(selected)}))
