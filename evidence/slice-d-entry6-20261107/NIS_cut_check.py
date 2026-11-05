"""Conservative source/cut audit. Experimental probes never imply row credit."""
from pathlib import Path
import re,json,hashlib,subprocess,lzma
E=Path(__file__).resolve().parent;R=E.parents[1]
sha=lambda b:hashlib.sha256(b).hexdigest()
def patch(name):return ''.join(l[1:] for l in (E/name).read_text().splitlines(True) if l.startswith('+') and not l.startswith('+++'))
def body(text,name):
 m=re.search(r'\bfn '+name+r'\s*\(',text);assert m,name
 a=text.index('{',m.end());i=a+1;depth=1
 while depth:depth+=(text[i]=='{')-(text[i]=='}');i+=1
 return text[a:i]
tokens=lambda s:re.findall(r'\w+|[^\w\s]',re.sub(r',\s*\]',']',s))
frozen=subprocess.check_output(['git','show','4bb3b3f51e16b4525f1d10336e2b0bcbbd775387:programs/r1-cost-probe/src/r1_pool_adapter_owned.rs'],cwd=R,text=True)
sdk=patch('NIS_sdk.patch');rows=[]
for source,target,count in [('stage1','first_cut',3),('stage2','second_cut',7)]:
 s=body(frozen,source);s=s[s.index('let owned = ['):];s=s[:s.index('];')+2]
 original=s
 s=s.replace('let owned','let _owned')
 s=re.sub(r'\bsnapshot\(([^()]*)\)',lambda m:'record('+m[1]+',log)',s)
 assert tokens('{'+s+'}')==tokens(body(sdk,target))
 rows.append(dict(source=source,target=target,ports=count,frozen_span_sha256=sha(original.encode()),exact_argument_expressions=True,return_value_association='OPEN: unit instrumentation is only an argument-expression cut, not a snapshot/OwnedAccount producer'))
assert not re.search(r'\bstatic\b|Option<fn|stub_verified',sdk)
forward=patch('NIS_forward.patch');assert 'code^1' in forward and 'log_wrong_child' in forward
assert not re.search(r'\bstatic\b|Option<fn|stub_verified',forward)
source_lib=subprocess.check_output(['git','show','4bb3b3f51e16b4525f1d10336e2b0bcbbd775387:programs/r1-cost-probe/src/lib.rs'],cwd=R,text=True)
assert 'return r1_pool_adapter::process(program_id,accounts,data);' in source_lib
source_process=subprocess.check_output(['git','show','4bb3b3f51e16b4525f1d10336e2b0bcbbd775387:programs/r1-cost-probe/src/r1_pool_adapter.rs'],cwd=R,text=True)
for call in ['stage1(program_id, accounts, data)','stage2(program_id, accounts, data)']:assert call in body(source_process,'process')
classification=[]
for i in range(46,121):
 a=f'NIS_K{i:03}';rc=json.loads((E/a/'receipt.json').read_text());log=lzma.decompress((E/a/'stdout.log.xz').read_bytes()).decode()
 kind='COMPILER_INPUT_FAILURE' if 'VERIFICATION:-' not in log else 'PASS' if 'VERIFICATION:- SUCCESSFUL' in log else 'FAILING_CONTROL' if 'VERIFICATION:- FAILED' in log and re.search(r'\*\* 1 of \d+ failed',log) and 'unwinding assertion' not in log else 'UNADMITTED'
 classification.append(dict(attempt=a,kind=kind,exit=rc['exit_status'],module=rc['module']))
 assert 'timed out' not in log.lower() and rc['exit_status'] not in [124,137]
findings=[dict(id='NIS-F1',kind='OWN_RUNNER_INPUT_FAILURE',attempts=[f'NIS_K{i:03}' for i in range(104,116)],finding='Generic stub had0 parameters for a1-parameter const-generic original. Queue mistook unnumbered Rust errors for control exits and consumed12 slots without any Kani verdict. No semantic credit. Same harness names retained; corrected generic signature; later queue requires an actual semantic verdict.'),dict(id='NIS-F2',kind='CALLER_DOMAIN_AND_RESULT_CARRIER_GAP',finding='Forwarding probes construct3/7 independent SDK cells with one-byte payloads and2/4-byte instruction data; logging reply is only Err(Custom), omitting Ok and other reachable ProgramError arms. These restrictions are not established by all runtime callers. Constructive corruption controls K096..103 improve fidelity but do NOT make the probes a complete(ak) caller packet. SDK log cuts return Unit and do not associate the complete OwnedAccount values, allocation/cleanup or exclusive write. No entry/process/wrapper row credit.'),dict(id='NIS-F3',kind='V1_DOMAIN_AND_MODEL_GAP',finding='V1 decoder native references cover lengths0..129 /0..193, excluding caller-admitted V2-sized256 /320 images. Universal wrong-length transport or separate native cases is required. Reference Charon emission and exact cohort/slot association are absent; the cold-cache preflight forbids extraction. V1 validators/decoders remain OPEN despite local Rust/reference passes.')]
out=dict(status='PASS_SOURCE_CUT_CHECK_WITH_OPEN_FINDINGS',snapshot_arguments=rows,native=classification,findings=findings,whole_entry_paths_closed=0,new_rows_from_these_probes=0)
(E/'NIS_CUT_ASSOCIATION.json').write_text(json.dumps(out,indent=1)+'\n')
print(json.dumps(dict(status=out['status'],source_ports=10,findings=len(findings),whole_entry_paths=0)))
