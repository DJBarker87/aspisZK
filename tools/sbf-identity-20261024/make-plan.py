#!/usr/bin/env python3
"""Emit a NON-EXECUTING release gate specification. Never launch its commands."""
import json,hashlib,subprocess,time,resource
from pathlib import Path
E=Path('evidence/sbf-identity-20261024');start=time.monotonic();a=json.load(open(E/'immutable-assessment.json'))
OLD='/home/dombarker/project-offloads/codex-cx-s10-repin3-20261023';NEW='/home/dombarker/project-offloads/codex-cx-sbf-identity-20261024'
pins={'default':'f8c0ec72621fd5029a97d796c4a3623d0dc44a8e7074122372f9872915d143d4','devnet':'63ad3e9cc096dcbb55b3ca7ac7c8e89e6a845796ab5e4f5b7d15db96f3784299','pool':'121f3e29741f510e6dc42d0345fc3c36217600f0be337094855c4a9da2581548'}
builds=[]
for m,v in a['modes'].items():
 cmd=[x.replace(OLD,NEW).replace('build-'+m+'-v1','capture-'+m+'-v1') for x in v['command']['command']]
 env={k:s.replace(OLD,NEW).replace('build-'+m+'-v1','capture-'+m+'-v1') for k,s in v['command']['env'].items()}
 env.update(PATH='/home/dombarker/.cargo/bin:/usr/bin:/bin',CARGO_HOME='/home/dombarker/.cargo',CARGO_NET_OFFLINE='true')
 name='aspis_pool.so' if m=='pool' else 'aspis_r1_cost_probe_program.so'
 builds.append(dict(mode=m,cwd=NEW+'/src',command=cmd,environment=env,unset_environment=['RUSTFLAGS']+([] if m=='devnet' else ['ASPIS_R1_POOL_PROGRAM_ID','ASPIS_R1_REGISTRY_PROGRAM_ID']),scope_command=['systemd-run','--user','--scope','--unit=sbf-identity-20261024-'+m+'-v1','-p','MemoryHigh=6G','-p','MemoryMax=8G','-p','MemorySwapMax=0','-p','TasksMax=64','/usr/bin/time','-v','-o',NEW+'/capture-'+m+'-v1/time.log','timeout','600',*cmd],expected_phase='optimized SBF compilation and retained MIR/LLVM emission; no proving, arithmetic, extraction or bootstrap',output=NEW+'/capture-'+m+'-v1/artifacts/'+name,linked_output=env['CARGO_TARGET_DIR']+'/sbpf-solana-solana/release/'+name,expected_sha256=pins[m],expected_bytes=v['artifact-comparison']['bytes'],historical_predecessor=v['receipt'],historical_command_sha256=a['inputs']['docs/research/100bit-spend-path-20261013/evidence/s10-repin3-20261023/build-'+m+'-v1/command.json']['sha256']))
deps={n:dict(sha256=hashlib.sha256((E/n).read_bytes()).hexdigest(),bytes=(E/n).stat().st_size) for n in ['current-content.json','current-drivers.json','current-global.json','current-source-tree.json','immutable-assessment.json','platform-release.txt','official-source-comparison.json','complete-source-comparison.json']}
r=dict(schema='sbf-identity-future-P7-plan-v1',status='PROPOSED ONLY; not executable authorization; no gate launched',source_revision=a['source_revision'],immutable_receipt_base=a['base'],stage=NEW,source_manifest=a['source_input_manifest'],source_input_count=7978,source_materialization='Materialize exactly source-inputs.json file list from immutable Git objects at frozen source; verify every size/SHA-256, file type/mode and symlink before use. Stop on any missing, extra or differing input. Do not populate the full repository or follow another worker path.',wrapper=dict(immutable_git_source=a['base']+':tools/s10-repin3-20261023/rustc-diagnostics.py',destination=NEW+'/rustc-diagnostics.py',sha256='fa74d69e097b6eab43809943614133081abb6beb19406018961402b86494ff84'),builds=builds,dependencies=deps)
(E/'recapture-plan.json').write_text(json.dumps(r,indent=2)+'\n')
u=resource.getrusage(resource.RUSAGE_SELF)
(E/'plan-generation-receipt.json').write_text(json.dumps(dict(command=['python3','tools/sbf-identity-20261024/make-plan.py'],source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),script_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),dependencies=deps,exit=0,wall_seconds=time.monotonic()-start,peak_rss_bytes=u.ru_maxrss,swaps=u.ru_nswap,print_axioms='N/A: plan generation only'),indent=2)+'\n')
print('Wrote proposed commands only; build/ELF/proof gates: 0')
