#!/usr/bin/env python3
"""Audit exact complete tx1 extraction and its conditional consuming theorem."""
from pathlib import Path
import hashlib,importlib.util,json,re,resource,subprocess,sys,time
started=time.monotonic();here=Path(__file__).resolve().parent;area=here.parents[1];repo=here.parents[4]
evidence=area/'evidence/cu-equivalence-20261019';read=lambda p:json.loads(p.read_text());sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
source_check=json.loads(subprocess.check_output([sys.executable,str(here/'extract-gamma-callers.py'),'--check'],text=True))
emission_check=json.loads(subprocess.check_output([sys.executable,str(here/'emit-gamma-callers.py'),'--check'],text=True))
pins=read(here/'cu-gamma-caller-input/source-pins.json')
# The exact new wrappers remain the frozen tip's callers, even though the
# shared finish body later changed for the other retained candidates.
spec=importlib.util.spec_from_file_location('cut',area/'tools/public-serializer-extraction-kit/extract.py');cut=importlib.util.module_from_spec(spec);spec.loader.exec_module(cut)
class Source:
 def __init__(self,raw):self.raw=raw
 def read_bytes(self):return self.raw
path='crates/aspis-r1-cost-probe/src/verifier.rs';tip=pins['production_revision']
current=(repo/path).read_bytes();assert current==subprocess.check_output(['git','-C',str(repo),'show',tip+':'+path])
for name,anchor in [('tx1','#[inline(never)]\npub fn tx1<'),('tx1-prepare','#[inline(never)]\nfn tx1_prepare<')]:
 item,*_=cut.find_item(Source(current),anchor)
 assert item==(here/'cu-gamma-caller-input/fragments'/('new-'+name+'.rs')).read_bytes(),name
externals=(area/'lean/AspisR1CuGammaCall/FunsExternal.lean').read_text()
assert 'import AspisR1CuGammaCall.Types' in externals
assert not re.search(r'^\s*(axiom|sorry|admit)\b',externals,re.M)
fields=re.findall(r'^  (\w+) :',externals,re.M)
assert fields==['verifyObserved','parse','accumulatorNew','finish'],fields
assert not re.search(r'^(?:def|abbrev|axiom) (?:weights.powers|gamma_(?:old|new).Prepared)',externals,re.M)
attempts={
 'AspisR1CuGammaCall/Types':'cu-gamma-call-types-a',
 'AspisR1CuGammaCall/FunsExternal':'cu-gamma-call-externals-a',
 'AspisR1CuGammaCall/Funs':'cu-gamma-call-funs-a',
 'CuSavingsGammaTx1':'cu-gamma-tx1-a'}
records={}
for module,attempt in attempts.items():
 directory=evidence/attempt;r=read(directory/'receipt.json')
 assert r['source_sha256']==sha(area/'lean'/(module+'.lean'))==sha(directory/'source.lean'),module
 assert r['exit_status']==0 and r['uncapped_nuc'],module
 assert r['resource_authorization']=='User: status update. no nuc limits (2026-10-19)'
 assert r['cgroup_limits']=={'memory.high':'max','memory.max':'max','memory.swap.max':'max'},module
 assert not any(x.startswith('-M') for x in r['command']),module
 assert r['process_swaps']>=0 and r['cgroup_swap_bytes']>=0,module
 assert r['runner_sha256']==sha(here/'run-focused.py'),module
 log=r['print_axioms_output'];assert 'sorryAx' not in log and 'error:' not in log,module
 axioms={n.strip() for b in re.findall(r'depends on axioms:\s*\[([^\]]*)\]',log) for n in b.split(',')}
 assert axioms<={'propext','Classical.choice','Quot.sound'},(module,axioms)
 records[module]=dict(attempt=attempt,source_sha256=r['source_sha256'],receipt_sha256=sha(directory/'receipt.json'),
   process_swaps=r['process_swaps'],cgroup_swap_bytes=r['cgroup_swap_bytes'])
for attempt,status in [('cu-gamma-caller-charon-a',101),('cu-gamma-caller-charon-b',0),('cu-gamma-caller-aeneas-a',0)]:
 r=read(evidence/attempt/'receipt.json');assert r['exit_status']==status and r['uncapped_nuc'],attempt
 assert r['limits']=={'memory.high':'max','memory.max':'max','memory.swap.max':'max'},attempt
 assert r['resource_authorization']=='User: status update. no nuc limits (2026-10-19)'
 if status==0:assert r['source_pins_sha256']==sha(here/'cu-gamma-caller-input/source-pins.json')
 if 'aeneas' in attempt:assert '-checks' in r['command'] and '-abort-on-error' in r['command']
failed=evidence/'cu-gamma-caller-charon-a';p=read(failed/'source-pins.json')
assert sha(failed/'source-pins.json')==read(failed/'receipt.json')['source_pins_sha256']
assert sha(failed/'input-lib.rs')==p['kit_files']['lib.rs']
usage=resource.getrusage(resource.RUSAGE_SELF)
print(json.dumps(dict(status='CHECKED_ACTUAL_TX1_EQUIVALENCE_CONDITIONAL_ON_LOCAL_CLAIM_FACTOR',targets=records,
 source_check=source_check,emission_check=emission_check,current_wrappers_byte_identical=True,
 preparation_bodies='Imported actual AspisR1CuGamma.Funs declarations, no new preparation parameters or axioms.',
 scope='Complete candidate-1 tx1 result/error/divergence equality under explicit claim-factor source equation and original shared helper boundaries. Full oracle/settlement/security transfer remains separate.',
 full_goal_complete=False,source_revision=subprocess.check_output(['git','-C',str(repo),'rev-parse','HEAD'],text=True).strip(),
 command=[sys.executable,str(Path(__file__).relative_to(repo))],features=['r0','private-leaf-salts'],exit_status=0,
 wall_seconds=time.monotonic()-started,peak_rss_bytes=usage.ru_maxrss if sys.platform=='darwin' else usage.ru_maxrss*1024,
 process_swaps=usage.ru_nswap,print_axioms='N/A: source and receipt audit; exact per-target axiom outputs checked above')))
