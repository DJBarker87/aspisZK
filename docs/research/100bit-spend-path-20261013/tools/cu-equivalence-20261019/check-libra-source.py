#!/usr/bin/env python3
"""Pin exact candidate-14 source delta, explicit signature transport and re-pins.
This audit does not itself claim the final equivalence theorem has passed.
"""
from pathlib import Path
import hashlib,json,re,resource,subprocess,sys,time
started=time.monotonic();tool=Path(__file__).resolve().parent;area=tool.parents[1];repo=tool.parents[4];ev=area/'evidence/cu-equivalence-20261019';sha=lambda b:hashlib.sha256(b).hexdigest()
git=lambda *args:subprocess.check_output(['git','-C',str(repo),*args])
candidate='39c2971dd16c95858a4cfd2c9ae35da052eacfa9';parent='16724ebd0bc2cb38f0115681386ecb4f12ceddc7';path='crates/aspis-r1-cost-probe/src/weights.rs'
assert git('rev-parse',candidate+'^').decode().strip()==parent
assert git('diff','--name-only',parent,candidate).decode().splitlines()==[path]
assert git('diff',candidate,'--','crates','programs')==b''
for script in ['extract-libra.py','emit-libra.py']:
 subprocess.run([sys.executable,str(tool/script),'--check'],check=True,capture_output=True)
pins=json.loads((tool/'libra-input/source-pins.json').read_text());assert pins['candidate']==candidate and pins['parent']==parent
for name,h in pins['kit_files'].items():assert sha((tool/'libra-input'/name).read_bytes())==h,name
for p in pins['fragments']:
 source=git('show',p['revision']+':'+p['path']);assert sha(source)==p['file_sha256']
 assert sha(source[p['start_byte']:p['end_byte_exclusive']])==p['fragment_sha256']
for attempt in ['libra-source-charon-a','libra-source-aeneas-b']:
 r=json.loads((ev/attempt/'receipt.json').read_text());assert r['exit_status']==0
 assert r['source_pins_sha256']==sha((tool/'libra-input/source-pins.json').read_bytes())
def item(data,name):
 m=re.search(rb'\bfn '+name.encode()+rb'(?:\s*\(|<)',data);assert m,name
 begin=m.start();op=data.index(b'{',m.end());end=op+1;depth=1
 while depth:depth+=(data[end:end+1]==b'{')-(data[end:end+1]==b'}');end+=1
 return begin,end,data[begin:end]
cur=git('show',candidate+':'+path);old=git('show',parent+':'+path)
for name in ['twofold_libra_weights','scalar_factor','kpowers','powers']:
 assert item(cur,name)[2]==item(old,name)[2],name
old_pair=item(old,'pair')[2];new_pair=item(cur,'pair')[2]
old_call=b'let libra=twofold_libra_weights(&low,self.extra);'
new_call=b'let libra=if self.variant==Variant::S2 {factored_s2_libra_weights(&ap0,&ap1,self.extra)}else{twofold_libra_weights(&low,self.extra)};'
assert old_pair.count(old_call)==new_pair.count(new_call)==1
assert new_pair.replace(new_call,old_call)==old_pair
contexts=tool/'libra-source-contexts';contexts.mkdir(exist_ok=True)
for name,data in [('pair-parent.rs',old_pair),('pair-candidate.rs',new_pair)]: (contexts/name).write_bytes(data)
caller=dict(source_path=path,parent_source_text_sha256=sha(old_pair),candidate_source_text_sha256=sha(new_pair),only_replacement={'parent':old_call.decode(),'candidate':new_call.decode()},binding='The original low16 constructor and every statement surrounding the call are identical. The S2 helper equality is substituted under the existing compositional source/runtime boundary; non-S2 call unchanged. No separately extracted full transaction body is claimed.')
raw=(tool/'libra-generated/Funs.lean').read_text();installed=(area/'lean/AspisR1Libra/Funs.lean').read_text()
# Verify each complete raw callback body survives promotion verbatim; changes are
# only trait dictionary fields, mutable-builder call names and Shared binder.
callback_names=['kpowers.closure.Insts.CoreOpsFunctionFnMutTupleUsizeQM31.call_mut','kpowers.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeQM31.call_once','old.twofold_libra_weights.closure.closure.Insts.CoreOpsFunctionFnMutTupleUsizeQM31.call_mut','old.twofold_libra_weights.closure.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeQM31.call_once']
def lean_decl(text,name):
 pat=r'(?m)^def\s+'+re.escape(name)+r'(?=\s|\n)';m=re.search(pat,text);assert m,name
 end=text.find('\n/--',m.end());end=len(text) if end<0 else end
 return text[m.start():end]
for name in callback_names:assert lean_decl(raw,name)==lean_decl(installed,name),name
assert (tool/'libra-generated/Types.lean').read_bytes()==(area/'lean/AspisR1Libra/Types.lean').read_bytes()
# Digest32-style inventory: original owner pair plus newly added helper. Caller
# dispatch is source-bound as the exact sole expression replacement above.
names=re.findall(r'(?m)^def\s+([A-Za-z_][A-Za-z_0-9.]*)',raw);declarations=[]
for name,owner in [('factored_s2_libra_weights','weights::factored_s2_libra_weights'),('pair','weights::Weights::pair')]:
 a,b,data=item(cur,name)
 extracted=['AspisR1Libra.'+n for n in names if n.startswith('new.factored_s2_libra_weights')]
 if name=='pair':extracted+=['AspisR1LibraLow.low','AspisR1CanonicalInputs.weights.powers','AspisR1.CuSavingsLibraCandidate14.production_equivalence','AspisR1.CuSavingsLibraCandidate14.caller_context']
 declarations.append(dict(classification='new-source-bound',cone='S2-Libra-factorization',rust_owner=owner,kind='fun_decls',source_path=path,current_start_byte=a,current_end_byte_exclusive=b,current_file_sha256=sha(cur),source_text_sha256=sha(data),historical_llbc_source_file=path,historical_span={'beg':{'line':cur[:a].count(b'\n')+1,'col':0},'end':{'line':cur[:b].count(b'\n')+1,'col':1}},extracted_lean_declarations=extracted,statement_diff='',notes=('Exact complete helper source emitted. Existing source arithmetic interpreted by proved concrete canonical/exact tower bridge; no factorization equivalence assumed.' if name!='pair' else 'Exact original pair source differs only in the selector expression pinned by this audit. Dispatch/low/power consumers must be re-pinned; no independently extracted complete Weights.pair module is represented as checked.')))
(ev/'LIBRA-CANDIDATE14-DECLARATION-REPIN.json').write_text(json.dumps(dict(schema_reference='design/J1-DIGEST32-EXTRACTED-DECLARATION-REPIN-20261016.json',candidate=candidate,parent=parent,counts={'new-source-bound':2},declarations=declarations),indent=2)+'\n')
report=dict(status='SOURCE_BINDINGS_AND_SIGNATURE_TRANSPORT_AUDITED_NOT_FINAL_PROOF_STATUS',candidate=candidate,parent=parent,source_pins_sha256=sha((tool/'libra-input/source-pins.json').read_bytes()),caller=caller,emission={'raw_types_sha256':sha((tool/'libra-generated/Types.lean').read_bytes()),'raw_funs_sha256':sha(raw.encode()),'installed_funs_sha256':sha(installed.encode()),'raw_callback_bodies_unchanged':callback_names,'signature_transports':['Two mutable FnMut dictionary fields invoke the exact emitted call_once, which applies the exact call_mut handback before returning updated closure state.','Two FnOnce dictionary fields project the value after that same exact emitted call_once.','Two from_fn call sites use the mutable source-runtime wrapper that retains final captures; the original caller discards the second returned item.'],'kernel_checks':['CuSavingsLibraSourceHandback.power_callback','CuSavingsLibraSourceHandback.reference_power_callback','CuSavingsLibraSourceHandback.mutable_builder_projection','CuSavingsLibraSourceProjection.power_once_projection','CuSavingsLibraSourceProjection.reference_once_instance_projection'],'array_source_admission':'CuSavingsArrayFromFn.source_eq_build (existing boundary/primitive interpretation)'} ,production_source_changed=False,audit=dict(command=[sys.executable,*sys.argv],source_revision=git('rev-parse','HEAD').decode().strip(),features=[],exit_status=0,wall_seconds=time.monotonic()-started,peak_rss_kib=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss//1024,process_swaps=resource.getrusage(resource.RUSAGE_SELF).ru_nswap,print_axioms='N/A: source audit; kernel checks recorded by focused Lean receipts.'))
(ev/'LIBRA-CANDIDATE14-SOURCE.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps(dict(status=report['status'],owners=2,raw_callbacks_preserved=4)))
