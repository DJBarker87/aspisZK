#!/usr/bin/env python3
"""Pin the exact decode-reuse delta; distinguish source checks from Lean proofs."""
from pathlib import Path
import argparse,hashlib,importlib.util,json,re,resource,subprocess,sys,time
started=time.monotonic()
ap=argparse.ArgumentParser();ap.add_argument('--check',action='store_true');args=ap.parse_args()
here=Path(__file__).resolve().parent;repo=here.parents[4];area=here.parents[1]
revision='39c2971dd16c95858a4cfd2c9ae35da052eacfa9';candidate='e5a93db5c9a4883245dc575eaa94742f9adeb629'
parser=area/'tools/public-serializer-extraction-kit/extract.py'
spec=importlib.util.spec_from_file_location('source_cut',parser);cut=importlib.util.module_from_spec(spec);spec.loader.exec_module(cut)
sha=lambda b:hashlib.sha256(b).hexdigest()
lib='programs/r1-cost-probe/src/lib.rs';adapter='programs/r1-cost-probe/src/r1_pool_adapter.rs'
files={path:subprocess.check_output(['git','-C',str(repo),'show',revision+':'+path]) for path in [lib,adapter]}
for path,raw in files.items():assert raw==(repo/path).read_bytes(),path
# The source parser works on paths; immutable snapshots also retain exact old spans.
outputs={};spans={}
def item(label,path,anchor,rev):
    data=subprocess.check_output(['git','-C',str(repo),'show',rev+':'+path])
    target=here/'public-decode-source'/('snapshot-'+label+'.rs')
    if not args.check:target.parent.mkdir(exist_ok=True);target.write_bytes(data)
    else:assert target.read_bytes()==data
    body,start,end,line,last=cut.find_item(target,anchor)
    outputs[label+'.rs']=body
    spans[label]=dict(revision=rev,path=path,file_sha256=sha(data),start_byte=start,end_byte_exclusive=end,
        first_line=line,end_line_exclusive=last,sha256=sha(body))
    return body
old=item('old-first',lib,'#[inline(never)]\nfn first(',candidate+'^')
new=item('new-first',lib,'#[inline(never)]\nfn first(',revision)
decoded=item('first-decoded',lib,'#[inline(never)]\nfn first_decoded(',revision)
old_stage=item('old-stage1',adapter,'#[inline(never)]\nfn stage1(',candidate+'^')
new_stage=item('new-stage1',adapter,'#[inline(never)]\nfn stage1(',revision)
box=item('decode-box',adapter,'#[inline(never)]\nfn decode_public_statement_box(',revision)
assert box in subprocess.check_output(['git','-C',str(repo),'show',candidate+'^:'+adapter])
old_call=b'super::first(&public_data, &proof_data[proof_start..proof_end], data[1] as usize)?'
new_call=b'super::first_decoded(statement.semantic_public(), &public_data, &proof_data[proof_start..proof_end], data[1] as usize)?'
assert new_stage.count(new_call)==1 and old_stage.count(old_call)==1
assert new_stage.replace(new_call,old_call)==old_stage,'stage1 changed beyond the single call replacement'
compact=lambda b:re.sub(rb'\s+',b'',b)
new_call_first=b'first_decoded(statement.semantic_public(),public_bytes,proof,k)'
assert new.count(new_call_first)==1
# Inline the exact wrapper, substituting only its public parameter. Both
# semantic_public and observer retain their original evaluation positions.
wrapper_body=decoded[decoded.index(b'{')+1:decoded.rindex(b'}')].strip()
assert compact(wrapper_body)==compact(b'verifier::tx1(public,public_bytes,proof,k,SolanaDigest,observer()).map_err(error)')
expanded=new.replace(new_call_first,b'let public=statement.semantic_public();\n'+wrapper_body)
assert compact(expanded)==compact(old),'factoring first altered more than the checked inline substitution'
# Check the exact immutable byte binding and first decoder at the caller.
pre=new_stage[:new_stage.index(new_call)]
assert pre.count(b'let public_data = public_account.try_borrow_data()?;')==1
assert pre.count(b'let statement = decode_public_statement_box(&public_data)?;')==1
assert b'let mut public_data' not in pre and b'let mut statement' not in pre
assert b'&mut public_data' not in pre and b'&mut statement' not in pre
assert pre.count(b'let public_data')==1 and pre.count(b'let statement')==1
assert b'decode_pool_v1_pair_forest_terminal_statement_v1(bytes)' in box
assert b'.map_err(|_| ProgramError::InvalidAccountData)?' in box
# Verify the complete old emitted caller body after explicit generic bindings.
old_model=area/'lean/ExtractedFirstCallerReachability.lean'
new_model=area/'lean/CuSavingsPublicDecodeSource.lean'
raw=old_model.read_bytes();bound=new_model.read_bytes()
old_first=raw[raw.index(b'def first {'):raw.index(b'private theorem bind_success')]
new_first=bound[bound.index(b'def sourceFirst {'):bound.index(b'theorem map_error_eq')]
old_body=compact(old_first.split(b':= do',1)[1])
new_body=compact(new_first.split(b':= do',1)[1])
replacements=[
 (b'core.result.Result.map_err',b'AspisR1PublicPreparation.core.result.Result.map_err'),
 (b'pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1.semantic_public',b'B.select'),
 (b'decodepublic_bytes',b'B.decodebytes'),
 (b'invalidAccountData',b'invalid'),
 (b'tx1public1public_bytesproofk()(somemark)',b'B.tx1public1bytesproofkobs'),
 (b'r2error',b'r2B.error'),
 (b'(alloc.vec.VecU8)',b'O')]
transformed=old_body
for before,after in replacements:
 assert before in transformed,before
 transformed=transformed.replace(before,after)
assert transformed==new_body,'The full emitted first body changed beyond documented boundary binding'
source_decoded=bound[bound.index(b'def sourceDecoded {'):bound.index(b'/-- Complete historical first body')]
decoded_body=source_decoded.split(b':= do',1)[1]
decoded_body=decoded_body.replace(b'let result \xe2\x86\x90',b'let r2 \xe2\x86\x90').replace(b') result B.error',b') r2 B.error')
decoded_body=re.sub(rb'\bpub\b',b'public1',decoded_body)
suffix=new_body[new_body.index(b'letr2'):new_body.index(b'|core.ops.control_flow.ControlFlow.Break')]
assert compact(decoded_body)==suffix,'New decoded wrapper changed the old tx1/map_err suffix'
pins=dict(production_revision=revision,candidate=candidate,cuts=spans,
    whole_stage1_identical_except_call=True,first_wrapper_inlining_identical=True,
    boxed_decoder_body_unchanged=True,same_immutable_public_bytes=True,
    source_semantics_claim='Exact source spans, immutable bindings and body identity after explicitly recorded inlining/context replacement. This checker is not a Rust semantics or SDK refinement theorem.',
    formal_model='CuSavingsPublicDecode',
    original_caller_body_sha256=sha(old_model.read_bytes()),source_binding_sha256=sha(new_model.read_bytes()),
    caller_body_binding_replacements=[(a.decode(),b.decode()) for a,b in replacements],
    complete_caller_body_binding_checked=True,decoded_suffix_binding_checked=True,
    open_binding='Boxed decoder, immutable account/runtime and adapter interpretation retain their explicit original source-model boundary; final security transfer is separate from these text checks.',
    outputs={name:sha(raw) for name,raw in outputs.items()})
outputs['source-pins.json']=(json.dumps(pins,indent=2)+'\n').encode()
for name,data in outputs.items():
    target=here/'public-decode-source'/name
    if args.check:assert target.read_bytes()==data,name
    else:target.parent.mkdir(exist_ok=True);target.write_bytes(data)
usage=resource.getrusage(resource.RUSAGE_SELF)
print(json.dumps(dict(check=args.check,source_delta_checked=True,wall_seconds=time.monotonic()-started,
    peak_rss_bytes=usage.ru_maxrss if sys.platform=='darwin' else usage.ru_maxrss*1024,process_swaps=usage.ru_nswap,
    source_revision=subprocess.check_output(['git','-C',str(repo),'rev-parse','HEAD'],text=True).strip(),
    command=[sys.executable,str(Path(__file__).relative_to(repo)),*sys.argv[1:]],exit_status=0,
    print_axioms='N/A: source-span and inlining checks; Lean theorem receipts are separate')))
