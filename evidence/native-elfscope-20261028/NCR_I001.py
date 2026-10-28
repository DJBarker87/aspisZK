import pathlib,json,subprocess
h=pathlib.Path('/home/dombarker/project-offloads/codex-cx-lowering2-20261026')
print('LOWERING_WORKSPACE',[(n,(h/n).exists()) for n in ['src','sbf-target-verifier','rustc-diagnostics.py']])
print('DISK',subprocess.check_output(['df','-h',str(h)]).decode())
for base in [pathlib.Path('/home/dombarker/.cargo/registry/src'),h/'src']:
 if not base.exists():continue
 for name in ['solana-sha256-hasher-2.3.0','solana-pubkey-2.4.0','solana-program-entrypoint-2.3.0','solana-cpi-2.2.1','solana-msg-2.2.1']:
  for d in base.glob('*/'+name):
   for p in d.glob('src/*.rs'):
    print('SDK_FILE',p);print(p.read_text())
print('CACHE_SIZE',subprocess.check_output(['du','-sh',str(h/'sbf-target-verifier')]).decode() if (h/'sbf-target-verifier').exists() else 'absent')
