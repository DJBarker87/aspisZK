#!/usr/bin/env python3
"""Verify exact extraction snapshots, retained failures, and focused kernel receipts."""
from pathlib import Path
import gzip,hashlib,json,re,subprocess
base=Path(__file__).resolve().parent
repo=base.parents[4]
sha=lambda raw:hashlib.sha256(raw).hexdigest()
def raw(p):
 return p.read_bytes() if p.exists() else gzip.decompress(p.with_name(p.name+'.gz').read_bytes())
for run in sorted((base/'extraction').iterdir()):
 for p,h in json.loads((run/'artifact-pins.json').read_text()).items():assert sha(raw(run/p))==h,(run.name,p)
 commands=json.loads((run/'commands.json').read_text())
 assert commands[-2]['name']=='charon' and commands[-2]['exit']==0
 expected=2 if run.name in ['prefix-a','prefix-b-experiment'] else 0
 assert commands[-1]['name']=='aeneas' and commands[-1]['exit']==expected
 for command in commands:
  assert command['swap_current_bytes']==0
  assert all(int(line.split()[1])==0 for line in command['events_after'].splitlines())
 llbc=json.loads(raw(run/'PrefixInto.llbc'));assert not llbc['has_errors'] and llbc['translated']['ordered_decls']
 pins=json.loads((run/'source/source-pins.json').read_text())
 for f,h in pins['kit_files'].items():assert sha((run/'source'/f).read_bytes())==h
 assert sha((run/'tool-inventory.json').read_bytes())=='b3b5117fb70cda0dfe44968f0e9b2c760dd3f479dfa4b505b41ec7034d489049'
actual=base/'extraction/prefix-e-exact'
production=subprocess.check_output(['git','-C',str(repo),'show','b38b1ce770f91a86315a3de1f750fbe993389569:crates/aspis-r1-cost-probe/src/r1_wire.rs'])
assert sha(production)=='4ce97b7bc11b495dc8af3ef79f29dbbd9ebba7c2427a6db1acb8851759b1d305'
kit=repo/'docs/research/100bit-spend-path-20261013/tools/prefix-aggregate-extraction-kit'
for n in ['lib.rs','Cargo.toml','source-pins.json','extract.py']:assert (actual/'source'/n).read_bytes()==(kit/n).read_bytes(),n
for p in (actual/'generated').rglob('*.lean'):
 assert not re.search(r'^\s*(axiom|opaque)\b|\bsorry\b',p.read_text(),re.M),p
 assert p.read_bytes()==(base/'lean/sources'/p.relative_to(actual/'generated')).read_bytes()
 assert p.read_bytes()==(repo/'docs/research/100bit-spend-path-20261013/lean/extracted-prefix-aggregate-20261016'/p.relative_to(actual/'generated')).read_bytes()
for run in (base/'lean/runs').iterdir():
 r=json.loads((run/'receipt.json').read_text())
 assert r['exit_status']==0 and r['process_swaps']==0 and r['cgroup_swap_current']=='0'
 assert r['limits']=={'memory.max':'8589934592','memory.high':'6442450944','memory.swap.max':'0'}
 assert '-j1' in r['command'] and '-M0' in r['command'] and not r['dependency_rebuild']
 assert sha((run/'source.lean').read_bytes())==r['source_sha256']
 assert sha((run/'runner.py').read_bytes())==r['runner_sha256']
 assert sha((base/'lean'/('input-manifest-'+run.name+'.json')).read_bytes())==r['input_manifest_sha256']
 assert r['olean_sha256'] and r['peak_process_rss_kib']>0 and 'libleanshared.so' in str(r['runtime_sha256'])
log=(base/'lean/runs/axioms-a/lean.log').read_text()
found=re.findall(r"'([^']+)' (?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)",log,re.S)
assert len(found)==16,len(found)
for name,axioms in found[:15]:assert set(a.strip() for a in axioms.split(',') if a.strip())<={'propext','Classical.choice','Quot.sound'},name
assert found[-1][0].endswith('Error.Insts.CoreFmtDebug.fmt') and 'Formatter' in found[-1][1] and '_native.decide' in found[-1][1]
for line in (base/'SHA256SUMS').read_text().splitlines():
 digest,p=line.split('  ',1);assert sha((base/p).read_bytes())==digest,p
print('PASS:5 retained extraction attempts; exact final production kit;3 Lean4.32 targets;15 standard-only declarations; unused Debug separately flagged')
