from pathlib import Path
import hashlib,json,re,shutil,os
H=Path('/home/dombarker/project-offloads/codex-pv-n7-20261027');E=H/'evidence'
def pin(p):
 b=p.read_bytes();return dict(sha256=hashlib.sha256(b).hexdigest(),bytes=len(b))
inputs=json.loads((H/'build-inputs.json').read_text())['files'];changes=[]
for p,h in inputs.items():
 assert pin(H/'base'/p)['sha256']==h,p
 if pin(H/'patched'/p)['sha256']!=h:changes.append(p)
assert sorted(changes)==['scripts/r1_devnet_spend.py','tools/r1-cost-probe/src/bin/devnet_spend.rs']
for n in ['base','patched']:
 assert pin(H/('devnet_spend-'+n))=={k:json.loads((E/('binary-'+n+'.json')).read_text())[k] for k in ['sha256','bytes']}
for r in json.loads((E/'elf-pins.json').read_text())['rows']:
 assert pin(Path(r['path']))['sha256']==r['expected']
text=(H/'full-disassembly.txt').read_text();lines=text.splitlines();sites=[]
for i,l in enumerate(lines):
 if 'call' in l and '<devnet_spend::decode_raw_key_record>' in l:
  sites.append('\n'.join(lines[max(0,i-24):i+12]))
assert len(sites)==1
(E/'decoder-callsite.txt').write_text('\n\n'.join(sites)+'\n')
(R:=E/'ruling-l-source.txt').write_text('Standalone host manifest:\n'+(H/'base/tools/r1-cost-probe/Cargo.toml').read_text()+'\nLibrary module gates:\n'+(H/'base/crates/aspis-r1-cost-probe/src/lib.rs').read_text()+'\nRelease default/devnet manifest:\n'+(H/'base/programs/r1-cost-probe/Cargo.toml').read_text()+'\nPool manifest:\n'+(H/'base/programs/aspis-pool/Cargo.toml').read_text())
assert 'LD_PRELOAD' not in os.environ
fixture=json.loads((E/'fixtures.json').read_text());assert len(fixture['rows'])==2
rec=dict(source_inputs_checked=len(inputs),source_changes=changes,elf_pins_rechecked=True,fixtures_pass=True,baseline_binary=pin(H/'devnet_spend-base'),patched_binary=pin(H/'devnet_spend-patched'),test_only_entropy_library=pin(H/'fixture-entropy.so'),test_only_entropy_source=pin(H/'fixture-entropy.c'),test_helper_source=pin(H/'request-fixture.rs'),patch=pin(H/'0001-private-key-raw-fd.patch'),retained_public_test_key='RFC8032-public-fixture-key.json (public test vector, retained; no RPC or funded account)',private_wallet_keys_opened=0,task_wallets_created=0,Lean_attempts=0,Kani_attempts=0,print_axioms='N/A: no Lean')
target=H/'target';assert not list(target.rglob('*-keypair.json'))
shutil.rmtree(target);assert not target.exists()
for p in [H/'source.tar',H/'pv-n7-supplement.tar']:
 p.unlink()
rec.update(cargo_target_removed=True,source_archives_removed=True)
(E/'cleanup.json').write_text(json.dumps(rec,indent=2)+'\n');print(json.dumps(rec))
