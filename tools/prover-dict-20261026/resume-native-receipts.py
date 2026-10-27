"""Audit and supplement resumed native receipts; no launches or binary copies."""
from pathlib import Path
import json,hashlib,subprocess
r=Path(__file__).resolve().parents[2];e=r/'docs/research/100bit-spend-path-20261013/evidence/prover-dict-20261026';sha=lambda x:hashlib.sha256(x).hexdigest()
std='tools/prover-dict-20261026/proof-std-native/lib.rs';final=(r/std).read_bytes();first=subprocess.check_output(['git','show','d8cc95ed63:'+std],cwd=r);invalid=final.replace(b'#[allow(invalid_atomic_ordering)]\n',b'')
for label,content in [('054',first),('058',invalid),('059',final),('060',final)]:
 p=e/'resume'/f'proof-std-{label}.rs.txt';p.write_bytes(content)
rows=[]
for f in sorted((e/'native').glob('pdict-*/receipt.json')):
 x=json.loads(f.read_text());name=x['attempt']
 try:n=int(name.rsplit('-',1)[1])
 except ValueError:continue
 if n<31:continue
 base='7fb276d44b' if n<=36 else '7fc5cfaa56' if n<=44 else '5e53c2ac86' if n<=57 else 'd8cc95ed63'
 supplement=dict(attempt=name,worktree_revision_at_invocation=base,raw_runner_source_revision=x['source_revision'],revision_qualification='The inherited runner labels the old owned-host snapshot revision. Worktree base plus exact retained WIP Rust/LLBC/dependency hashes qualify these focused results; no formal release revision identity is asserted.',embedded_kani_compiler='rustc1.93nightly53732d5e0, separately pinned in resume-provenance.json; inherited ambient rustc field is not the Kani compiler',native_kind='Kani' if 'kani' in x['target'] else 'Charon/Aeneas')
 if name.startswith('pdict-resume-') and 'kani' in x['target']:
  if '--manifest-path' in x['target']:
   assert n in [54,58,59,60]
   content=first if n==54 else invalid if n==58 else final
   supplement['extra_source_inputs']=[dict(path=std,sha256=sha(content),retained=f'resume/proof-std-{n:03d}.rs.txt')]
  else:
   h=x['source_sha256']['crates/aspis-r1-cost-probe/src/r1_wire.rs'];p=e/'native-source'/f'{h}.rs.txt';assert p.exists() and sha(p.read_bytes())==h
  rows.append(dict(attempt=name,exit=x['exit_status'],wall=x['wall_seconds'],rss=x['peak_rss_kib'],swaps=x['swaps'],cgroup_peak_bytes=x['cgroup_memory_peak_bytes'],scope=x['expected_work']))
 (f.parent/'resume-input-supplement.json').write_text(json.dumps(supplement,indent=2)+'\n')
assert len(rows)==12
(e/'resume/native-summary.json').write_text(json.dumps(dict(runs=rows,kani_runs=len(rows),passed=sum(z['exit']==0 for z in rows),timeout=sum(z['exit']==124 for z in rows),compilation_rejections=sum(z['exit']==1 for z in rows),remaining=15-len(rows),native_type_associations_still_open=[0,3,27],root_premises_removed=0),indent=2)+'\n');print('checked',len(rows),'native runs')
