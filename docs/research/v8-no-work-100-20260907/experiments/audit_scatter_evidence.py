#!/usr/bin/env python3
"""Collect source-pinned evidence without rerunning builds or Lean leaves."""
import hashlib,json,re
from pathlib import Path
ROOT=Path(__file__).resolve().parent.parent; EX=ROOT/'experiments'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def mac_metrics(log):
    return {'wall_seconds':float(re.search(r'([\d.]+) real',log)[1]),
      'peak_rss_bytes':int(re.search(r'(\d+)  maximum resident set size',log)[1]),
      'swaps':int(re.search(r'(\d+)  swaps',log)[1])}
leaves=[]
for stem,logname in [('CopyScatterNodes','nodes'),('CopyScatterCells30','cells30'),
    ('CopyScatterCells55','cells55'),('CopyScatterCells80','cells80'),('CopyScatterPlan','plan')]:
    p=EX/f'copy-scatter-{logname}-lean.log';log=p.read_text()
    assert not re.search(r'error:|sorryAx',log)
    axs=re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]",log)
    assert axs and all(set(filter(None,(v.strip() for v in ax.split(','))))<= {'propext','Classical.choice','Quot.sound'} for _,ax in axs)
    hs=sha(EX/f'{stem}.lean');assert hs in log
    oleans=re.findall(r'([a-f0-9]{64})\s+[^\n]+\.olean',log);assert len(oleans)==2
    if (EX/f'{stem}.olean').exists():assert sha(EX/f'{stem}.olean')==oleans[-1]
    leaves.append({'file':f'experiments/{stem}.lean','source_sha256':hs,'olean_sha256':oleans[-1],
      'exit':0,**mac_metrics(log),'axiom_declarations':[name for name,_ in axs],
      'log':str(p.relative_to(ROOT))})
def linux_metrics(path):
    log=path.read_text();elapsed=re.findall(r'Elapsed \(wall clock\) time .*?: (\S+)',log)[-1]
    parts=list(map(float,elapsed.split(':')));seconds=sum(x*60**i for i,x in enumerate(reversed(parts)))
    return {'exit':int(re.findall(r'Exit status: (\d+)',log)[-1]),'wall_seconds':seconds,
      'peak_rss_kib':int(re.findall(r'Maximum resident set size \(kbytes\): (\d+)',log)[-1]),
      'swaps':int(re.findall(r'Swaps: (\d+)',log)[-1]),'log':str(path.relative_to(ROOT))}
raw=json.loads((ROOT/'evidence/scatter/copy-scatter-max-v1/withdrawal-255-2-success.json').read_text())
prep=(ROOT/'evidence/scatter/copy-scatter-prepare.log').read_text()
hashes=re.findall(r'([a-f0-9]{64})\s+[^\n]+\.rs',prep)
assert len(hashes)==2 and hashes[1]==sha(EX/'copy_scatter_plan_generated.rs')
out={'schema':'aspis.research.v8.scatter-evidence.v1',
 'base_revision':'0fa310741d483db87e91c3e69aa109a65f88e267','date':'2026-09-09','research_only':True,
 'generator_sha256':sha(EX/'generate_copy_scatter.py'),
 'generated_rust_sha256':hashes[1],'nuc_copy_source_sha256':hashes[0],
 'nuc_task_copy':'/home/dombarker/project-offloads/aspis-v8-performance-20260908.scS2Jz',
 'table_sha256':json.loads((EX/'copy-scatter-plan.json').read_text())['table_sha256'],
 'lean':{'workspace':'/Users/dominic/ZK/AspisFormal','version':'4.32.0',
    'mathlib_revision':'81a5d257c8e410db227a6665ed08f64fea08e997',
    'mathlib_tactic_olean_sha256':'55ee2345729e8a4d379de3bce14ea18b14fbfdc259cf2653fadf4bf3a46876d8',
    'command':'bash experiments/run_copy_scatter_lean.sh <leaf> <new-log>',
    'leaves':leaves,'new_axioms_or_sorry':False,
    'scope':'Universal ring-valued equality of all 73 modified cells, public boolean selection lemma and named DAG sums. Not a Rust/Aeneas/parser/full-verifier translation.'},
 'rust_tests':linux_metrics(ROOT/'evidence/scatter/copy-scatter-test.log'),
 'sbf_build':linux_metrics(ROOT/'evidence/scatter/copy-scatter-sbf-build.log'),
 'limits':{'build_high_gib':5,'build_max_gib':7,'svm_high_gib':3,'svm_max_gib':4,'swap_max':0,'cargo_jobs':2},
 'artifacts':{role:raw['artifacts'][role] for role in ('selected_verifier','pool','registry','token_program')},
 'stack':json.loads((ROOT/'evidence/scatter/scatter-stack.json').read_text()),
 'verifier_elf_bytes':{'previous_tag7':908840,'scatter':965056,'increase':56216},
 'additional_heap_bytes':944,'new_proof_or_transcript_bytes':0,'proof_body_cap':40282,
 'runtime':{'litesvm':'0.16.0','solana_runtime':'4.2.1','sbf_tools':'v1.54','host_rust':'1.94.1','actual_transaction_cap':1200000},
 'failed_preflights':[
    {'log':'experiments/copy-scatter-root-preflight.log','exit':1,'reason':'Lean -o needs the external package root set with -R','wall_seconds':0.81,'peak_rss_bytes':669302784,'swaps':0},
    {'log':'experiments/copy-scatter-vector-preflight.log','exit':1,'reason':'73-entry vecCons definitional lookup hit recursion depth. Generator now emits three small indexed tables; no resource limit was raised.',**mac_metrics((EX/'copy-scatter-vector-preflight.log').read_text())}],
 'prover_time_or_rss_rerun':False,'global_security_certificate':None,'universal_cu_bound':None}
assert out['rust_tests']['exit']==out['sbf_build']['exit']==0
print(json.dumps(out,indent=2))
