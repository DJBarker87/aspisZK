#!/usr/bin/env python3
"""Pin gamma reuse sources and checked conditional caller theorems, not closure."""
from pathlib import Path
import hashlib,importlib.util,json,re,resource,subprocess,sys,time
started=time.monotonic()
here=Path(__file__).resolve().parent;area=here.parents[1];repo=here.parents[4]
evidence=area/'evidence/cu-equivalence-20261019'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
read=lambda p:json.loads(p.read_text())
kit_check=json.loads(subprocess.check_output([sys.executable,str(here/'extract-cu-gamma.py'),'--check'],text=True))
pins=read(here/'cu-gamma-input/source-pins.json')
# The only claim changes are its gamma-table parameter and moving this first
# computation out. This text check does not assert Rust semantic equivalence.
old=(here/'cu-gamma-input/fragments/old-claim.rs').read_bytes()
new=(here/'cu-gamma-input/fragments/new-claim.rs').read_bytes()
assert old.count(b'gamma:E')==1 and old.count(b'let g=powers::<29>(gamma);')==1
assert old.replace(b'gamma:E',b'g:&[E;29]',1).replace(b'let g=powers::<29>(gamma);',b'',1)==new
# Exact old/new tx1 wrappers at the candidate: no hidden change at this step.
spec=importlib.util.spec_from_file_location('cut',area/'tools/public-serializer-extraction-kit/extract.py')
cut=importlib.util.module_from_spec(spec);spec.loader.exec_module(cut)
class Source:
 def __init__(self,raw):self.raw=raw
 def read_bytes(self):return self.raw
candidate=pins['candidate'];path='crates/aspis-r1-cost-probe/src/verifier.rs'
wrappers={}
for name,anchor in [('prepare','#[inline(never)]\nfn tx1_prepare<'),('tx1','#[inline(never)]\npub fn tx1<')]:
 for label,rev in [('old',candidate+'^'),('new',candidate)]:
  raw=subprocess.check_output(['git','-C',str(repo),'show',rev+':'+path])
  body,*_=cut.find_item(Source(raw),anchor)
  wrappers[label+'-'+name]=body
old_prepare=wrappers['old-prepare'];new_prepare=wrappers['new-prepare']
assert new_prepare.replace(b',g:&mut [E;29]',b'',1).replace(b'Prepared::new(&sem,v,hash,g)',b'Prepared::new(&sem,v,hash)',1)==old_prepare
old_tx1=wrappers['old-tx1'];new_tx1=wrappers['new-tx1']
old_line=b'let (_semantic_claims,p)=tx1_prepare(public,&v,hash,obs)?;let mut a=Accumulator::new(v.variant)?;let g=powers::<29>(p.gamma);mark(obs,Phase::Prepare);'
new_lines=b'let mut g=[E::ZERO;29];\n    let (_semantic_claims,p)=tx1_prepare(public,&v,hash,obs,&mut g)?;let a=Accumulator::new(v.variant)?;mark(obs,Phase::Prepare);'
assert old_tx1.count(old_line)==1 and new_tx1.count(new_lines)==1
assert new_tx1.replace(new_lines,old_line)==old_tx1
raw_pins=read(here/'cu-gamma-emission-inputs.json')
for name,pin in raw_pins.items():assert sha(here/'cu-gamma-generated'/name)==pin,name
artifacts=read(evidence/'GAMMA-ARTIFACT-PINS.json')
assert artifacts['exit_status']==0 and artifacts['process_swaps']==0
remote='/home/dombarker/project-offloads/aspis-r1-cu-equivalence-20261019'
for name,pin in raw_pins.items():
 assert artifacts['files'][remote+'/generated-cu-gamma-prepared-b/AspisR1CuGamma/'+name]==pin,name
for name in ['CuGamma.llbc','CuGammaPrepared.llbc']:
 assert re.fullmatch('[0-9a-f]{64}',artifacts['files'][remote+'/'+name]),name

assert (area/'lean/AspisR1CuGamma/Types.lean').read_bytes()==(here/'cu-gamma-generated/Types.lean').read_bytes()
raw=(here/'cu-gamma-generated/Funs.lean').read_bytes()
model=(area/'lean/AspisR1CuGamma/Funs.lean').read_bytes()
assert model==raw.replace(b'namespace AspisR1CuGamma\n',b'namespace AspisR1CuGamma\n\nvariable [Boundaries]\n',1)
external=(area/'lean/AspisR1CuGamma/FunsExternal.lean').read_text()
assert 'class Boundaries where' in external and 'oldClaim :' in external and 'newClaim :' in external
assert not re.search(r'^\s*(axiom|sorry)\b',external,re.M)
assert not re.search(r'^import .*Template',external,re.M)
attempts={
 'AspisR1CuGamma/Types':'cu-gamma-types-b',
 'AspisR1CuGamma/FunsExternal':'cu-gamma-externals-a',
 'AspisR1CuGamma/Funs':'cu-gamma-funs-a',
 'CuSavingsGammaTable':'cu-gamma-table-d',
 'CuSavingsGammaCaller':'cu-gamma-caller-a',
 'CuSavingsGammaPreparation':'cu-gamma-preparation-d',
 'CuSavingsGammaTransfer':'cu-gamma-transfer-a'}
records={}
for module,attempt in attempts.items():
 directory=evidence/attempt;r=read(directory/'receipt.json')
 assert r['source_sha256']==sha(area/'lean'/(module+'.lean'))==sha(directory/'source.lean'),module
 assert r['exit_status']==0 and r['process_swaps']==0 and r['cgroup_swap_bytes']==0,module
 assert r['cgroup_limits']=={'memory.high':str(6*2**30),'memory.max':str(8*2**30),'memory.swap.max':'0'}
 assert sum(value for _,value in r['reservations'])<=50*2**30,module
 log=r['print_axioms_output'];assert 'sorryAx' not in log and 'error:' not in log
 axioms={n.strip() for b in re.findall(r'depends on axioms:\s*\[([^\]]*)\]',log) for n in b.split(',')}
 assert axioms<={'propext','Classical.choice','Quot.sound'},(module,axioms)
 records[module]=dict(attempt=attempt,receipt_sha256=sha(directory/'receipt.json'),source_sha256=r['source_sha256'])
emission=read(evidence/'cu-gamma-aeneas-prepared-b/receipt.json')
assert emission['exit_status']==0 and '-checks' in emission['command'] and '-abort-on-error' in emission['command']
assert emission['frontend_binary_sha256']=='4632746db1bf6c3953f2971078965a2a5a8ad6cf5f75636b46b397bc50c550b5'
assert emission['source_pins_sha256']==sha(here/'cu-gamma-input/source-pins.json')
assert emission['process_swaps']==0 and emission['cgroup_swap_current']=='0'
assert emission['command'][-1].endswith('/CuGammaPrepared.llbc')
for attempt,exit_status in [('cu-gamma-charon-a',0),('cu-gamma-charon-prepared-a',0),
 ('cu-gamma-aeneas-a',2),('cu-gamma-aeneas-prepared-a',2),('cu-gamma-aeneas-full-b',2)]:
 r=read(evidence/attempt/'receipt.json');assert r['exit_status']==exit_status,attempt
 assert r['process_swaps']==0 and r['cgroup_swap_current']=='0',attempt
 assert r['limits']['memory.swap.max']=='0' and int(r['limits']['memory.max'])<=8*2**30,attempt
 if 'aeneas' in attempt:assert '-checks' in r['command'],attempt
usage=resource.getrusage(resource.RUSAGE_SELF)
print(json.dumps(dict(status='CHECKED_GAMMA_DATAFLOW_AND_CONDITIONAL_CALLER_TRANSFER',targets=records,
 source_delta=dict(claim_suffix_byte_identical=True,tx1_prepare_only_scratch_parameter=True,
 tx1_only_scratch_init_and_call_replacement=True,source_interpretation_admitted=False),
 kit_check=kit_check,emission_receipt_sha256=sha(evidence/'cu-gamma-aeneas-prepared-b/receipt.json'),
 open_obligations=['Discharge local claim-factor contract from actual helper source under the reference boundary.',
 'Consume the combined theorem in admitted tx1_prepare/tx1 source contexts, preserving allocation/observer/error order.',
 'Compose all retained candidates and transfer soundness/privacy under their original premises.'],
 full_goal_complete=False,command=[sys.executable,str(Path(__file__).relative_to(repo))],
 source_revision=subprocess.check_output(['git','-C',str(repo),'rev-parse','HEAD'],text=True).strip(),
 features=['r0','private-leaf-salts'],exit_status=0,wall_seconds=time.monotonic()-started,
 peak_rss_bytes=usage.ru_maxrss if sys.platform=='darwin' else usage.ru_maxrss*1024,process_swaps=usage.ru_nswap,
 print_axioms='N/A: source/receipt audit; exact theorem audits checked above')))
