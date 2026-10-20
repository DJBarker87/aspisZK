#!/usr/bin/env python3
"""Focused post-relocation ELF identity and six-harness replay on the host."""
from pathlib import Path
import hashlib,json,os,subprocess
H=Path('/home/dombarker/project-offloads/codex-cx-asq8-kani-20261021')
F=Path('/home/dombarker/project-offloads/codex-cx-pin-20261020/artifacts')
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
inputs=json.loads((H/'source-inputs.json').read_text())
bad=[p for p,s in inputs.items() if sha(H/'src'/p)!=s]
assert not bad,bad
(H/'source-validation.json').write_text(json.dumps(dict(total=len(inputs),mismatches=bad),indent=2)+'\n')
env=dict(os.environ,PATH='/home/dombarker/.cargo/bin:/usr/bin:/bin',CARGO_BUILD_JOBS='4',RUSTFLAGS='-C link-arg=-Wl,--threads=4')
for k in ['ASPIS_R1_POOL_PROGRAM_ID','ASPIS_R1_REGISTRY_PROGRAM_ID','CARGO_ENCODED_RUSTFLAGS']:
 env.pop(k,None)
def run(name,note,cmd,e):
 subprocess.run(['python3',str(H/'harness/reservation.py'),str(H/f'reservation-{name}.json')],check=True,stdout=subprocess.DEVNULL)
 subprocess.run([str(H/'harness/capped-run.sh'),name,note,str(H/'src'),'--',*cmd],env=e,check=True)
identities=[]
for mode,pin,manifest,features,filename in [
 ('default','dfc2a91ab24e1ec4f57debd8f124cb4f6a3c38ba2662b7318e2e4f3b4acdde34','r1-cost-probe','pool-adapter,private-leaf-salts','aspis_r1_cost_probe_program.so'),
 ('devnet','fb2fc048f6499a4775051d0267c76e8ca273b28f557bfd3b5fb65b2f687c8b78','r1-cost-probe','pool-adapter,private-leaf-salts','aspis_r1_cost_probe_program.so'),
 ('pool','121f3e29741f510e6dc42d0345fc3c36217600f0be337094855c4a9da2581548','aspis-pool','r1-split-checkpoint,pair-forest-source-invariant-audit,pair-forest-source-result-invariant-audit','aspis_pool.so')]:
 e=dict(env,CARGO_TARGET_DIR=str(H/'sbf-target-pool'),CARGO_TARGET_SBPF_SOLANA_SOLANA_RUSTFLAGS='-C link-arg=--threads=4')
 if mode=='devnet':
  c=json.loads((H/'src/docs/research/100bit-spend-path-20261013/evidence/freeze-20261020/r1-devnet.template.json').read_text())
  e.update(ASPIS_R1_POOL_PROGRAM_ID=c['programs']['pool'],ASPIS_R1_REGISTRY_PROGRAM_ID=c['programs']['registry'])
 out=H/'artifacts'/('relocation-'+mode);out.mkdir(exist_ok=False)
 cmd=['env','-u','RUSTFLAGS','/home/dombarker/.local/share/solana/install/releases/3.1.13/solana-release/bin/cargo-build-sbf','--manifest-path',str(H/'src/programs'/manifest/'Cargo.toml'),'--sbf-out-dir',str(out),'--features',features,'--skip-tools-install','--offline','-j','4','--','--locked']
 run('relocation-build-'+mode,'Incremental optimized SBF compilation/link; frozen byte identity after EOF-only reference relocation',cmd,e)
 artifact=out/filename;frozen=F/mode/filename
 subprocess.run(['cmp','--',str(artifact),str(frozen)],check=True)
 assert sha(artifact)==sha(frozen)==pin
 identities.append(dict(mode=mode,sha256=pin,bytes=artifact.stat().st_size,byte_equal=True,frozen_path=str(frozen),artifact_path=str(artifact),receipt=f'receipts/relocation-build-{mode}/receipt.json'))
 (H/'relocation-elf-identities.json').write_text(json.dumps(identities,indent=2)+'\n')
for target in ['transfer_encoder_equivalence','withdrawal_encoder_equivalence','accepted_request_reencodes_exactly','request_decoder_equivalence','shipped_pipeline_normalization_equivalence','slice_array_header_comparison_model']:
 e=dict(env,CARGO_TARGET_DIR=str(H/'kani-target'))
 run('kani-relocation-'+target,'Kani compilation and symbolic '+target+' after source relocation; no arithmetic elimination',['cargo','kani','-p','aspis-statement','--lib','--exact','--harness','pool_v1::pair_forest_terminal::asq8_kani::'+target,'--no-assertion-reach-checks','--solver','kissat','--output-format','old','-Z','unstable-options','--cbmc-args','--unwinding-assertions'],e)
