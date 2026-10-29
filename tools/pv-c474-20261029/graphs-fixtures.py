"""Exact Cargo unit graphs (no compilation) and the existing fixed-coin fixture gate."""
from pathlib import Path
import hashlib,json,os,subprocess
H=Path('/home/dombarker/project-offloads/codex-pv-c474-20261029');R=H/'src'
sha=lambda b:hashlib.sha256(b).hexdigest()
env=dict(os.environ,PATH='/home/dombarker/.cargo/bin:/usr/bin:/bin',RUSTC_BOOTSTRAP='1')
for name,cwd,features,args in [('client',R/'tools/r1-cost-probe','r1p-check,aspis-r1-cost-probe/ct-host-prover',['--profile','client','--bin','devnet_spend']),('probes',R,'optimized-terminal,r1p-check,ct-host-prover',['--release','-p','aspis-r1-cost-probe','--example','prover_rw_differential','--example','prover_rw_gate'])]:
 env['RUSTFLAGS']='--cfg getrandom_backend="linux_raw" --check-cfg=cfg(getrandom_backend,values("linux_raw")) -C link-arg=-Wl,--threads=4' if name=='client' else '--cfg getrandom_backend="linux_raw" -C panic=abort -C link-arg=-Wl,--threads=4'
 env.pop('CARGO_ENCODED_RUSTFLAGS',None)
 cmd=['cargo','+1.94.1','build','--locked','--offline','-j','4','--features',features,*args,'-Z','unstable-options','--unit-graph']
 x=subprocess.run(cmd,cwd=cwd,env=env,capture_output=True,text=True,check=True)
 (H/(name+'-unit-graph.json')).write_text(x.stdout)
 (H/(name+'-unit-graph-command.json')).write_text(json.dumps(dict(command=cmd,environment={k:env[k] for k in ['RUSTC_BOOTSTRAP','RUSTFLAGS']},scope='Cargo unit graph only, no compilation/code generation; production builds unset RUSTC_BOOTSTRAP',stderr=x.stderr),indent=2)+'\n')
# Same two successful fixtures, same coin 0, existing D328 deterministic criterion.
subprocess.run([H/'probe-target/release/examples/prover_rw_gate',H/'fixed-fixtures','0','1'],check=True)
G=Path('/home/dombarker/project-offloads/codex-pv-gate6-20261028');pins=json.loads((G/'fixture-control-pins.json').read_text());rows=[]
B=Path('/home/dombarker/project-offloads/codex-pv-integ1-20261027/d298/baseline/fixtures-candidate')
for f in ['transfer','withdrawal']:
 a=B/(f+'-0');b=H/'fixed-fixtures'/(f+'-0');expected=pins[f]
 files={}
 for name,pin in expected['files'].items():
  av=(a/name).read_bytes();bv=(b/name).read_bytes();assert sha(av)==pin['sha256'] and len(av)==pin['bytes']
  files[name]=dict(identical=av==bv,baseline_sha256=sha(av),draft_sha256=sha(bv),bytes=len(bv))
 assert sha((a/'result.json').read_bytes())==expected['raw_result_json']['sha256']
 records={k:json.loads((p/'result.json').read_text()) for k,p in [('baseline',a),('draft',b)]}
 canonical={k:json.dumps({x:y for x,y in v.items() if x!='seconds'},sort_keys=True,separators=(',',':')) for k,v in records.items()}
 ledgers={k:{str(p.relative_to(v/'ledger')):dict(sha256=sha(p.read_bytes()),bytes=p.stat().st_size) for p in (v/'ledger').rglob('*') if p.is_file()} for k,v in [('baseline',a),('draft',b)]}
 assert ledgers['baseline']==expected['ledger_manifest']
 row=dict(fixture=f,files=files,canonical_records_identical=canonical['baseline']==canonical['draft'],canonical_records=canonical,ledger_identical=ledgers['baseline']==ledgers['draft'],ledger_manifest=ledgers)
 assert all(x['identical'] for x in files.values()) and row['canonical_records_identical'] and row['ledger_identical'],row
 rows.append(row)
(H/'fixed-fixture-comparison.json').write_text(json.dumps(dict(passed=True,coin=0,comparisons=rows,control_pins=pins,scope='Existing D328 deterministic fixed-coin gate, candidate rerun; retained golden control verified read-only, no unchanged control proof regeneration'),indent=2)+'\n');print('FIXED_FIXTURES_PASS',flush=True)
