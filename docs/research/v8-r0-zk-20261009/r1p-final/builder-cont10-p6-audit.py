#!/usr/bin/env python3
"""Bind each projected solver receipt to the exact tested Rust source variant."""
import pathlib,json,re,hashlib,subprocess
H=pathlib.Path(__file__).resolve().parent;ROOT=H.parents[3]
D=json.loads((H/'builder-cont10-host-evidence.json').read_text())
sha=lambda b:hashlib.sha256(b).hexdigest()
p=ROOT/'tools/r1-builder-reference/tree.rs';current=p.read_text()
old=re.sub(r'        } else \{ Err\(match kani::any::<u8>\(\) % 13 \{[\s\S]*?        \}\) \};\n        let source = \(\|\| \{',
 '        } else { Err(PoolV1TreeError::IndexOutOfRange) };\n        let source = (|| {',current)
assert old!=current
checks={};run_pins={}
for name in ['tree_validator_frontier_step','tree_validator_index_step','tree_validator_root_step','tree_validator_root_step-all-errors']:
 d=D['validator-steps/'+name];r=d['receipt']
 assert r['exit_status']==0 and r['swaps']==0
 assert r['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
 assert r['env']['RUSTFLAGS']=='-C link-arg=-Wl,--threads=4'
 assert 'VERIFICATION:- SUCCESSFUL' in d['logs']['stdout.log']
 count=re.search(r'0 of (\d+) failed',d['logs']['stdout.log']);assert count
 sources=D['drop-input-pins'][name+'-sources.json']
 for file,v in sources.items():
  data=(ROOT/file).read_bytes()
  if file=='tools/r1-builder-reference/tree.rs' and not name.endswith('-all-errors'):data=old.encode()
  assert sha(data)==v['sha256'],(name,file)
 checks[name]=dict(checks=int(count.group(1)),receipt=r,source_files=len(sources),tree_source_sha256=sources['tools/r1-builder-reference/tree.rs']['sha256'])
revision=subprocess.check_output(['git','rev-parse','e99f0ae38'],text=True).strip()
remote='''import pathlib,hashlib,json
R=pathlib.Path('/home/dombarker/project-offloads/codex-cx-builder-ref10-20261021')
ps=[R/'kani-source/Cargo.lock',pathlib.Path('/home/dombarker/.cargo/bin/cargo-kani'),pathlib.Path('/home/dombarker/.kani/kani-0.67.0/bin/kani-driver'),pathlib.Path('/home/dombarker/.kani/kani-0.67.0/bin/kani-compiler')]
print(json.dumps({str(p):dict(sha256=hashlib.sha256(p.read_bytes()).hexdigest(),size=p.stat().st_size) for p in ps}))'''
pins=json.loads(subprocess.check_output(['ssh','dombarker@100.108.41.90','python3 -'],input=remote,text=True))
result=dict(source_revision=revision,source_dirty_at_all_solver_runs=True,checked_source_variants=checks,tool_and_lock_pins_after_runs=pins,scope='projected index/frontier/root transitions only; no whole shipped validator or destructor verdict',all_current_shipped_rs_and_toml_pins_match=True,source_variant_note='First three receipts predate expansion of the root error selector; that sole tail change is reconstructed and hashed. Frontier/index harness bodies are unchanged.',named_trust_boundary='P6: Kani/CBMC soundness, projected source-expression and owned-array/iterator correspondence; not a Lean axiom',no_shipped_crate_or_program_change=not subprocess.check_output(['git','diff','e5d6d81a5','--name-only','--','crates','programs'],text=True).strip())
assert result['no_shipped_crate_or_program_change']
(H/'builder-cont10-p6-audit.json').write_text(json.dumps(result,indent=2)+'\n')
print('PASS: four source-bound projected receipts, all current shipped source pins, zero swaps')
