#!/usr/bin/env python3
"""Aspis freeze rehearsal: write the run config for the local validator (fv_local_config.py with the
source tree, the Pool address, the Pool ELF and the client binary as parameters).
usage: fv_frz_local_config.py <name> <verifier-elf> <pool-program-id> <pool-elf> <client-binary> <source-dir-name>"""
import hashlib, json, pathlib, subprocess, sys
W = pathlib.Path('/home/dombarker/project-offloads/future-version-20261111'); L = W / sys.argv[1]
VERIFIER, POOL, POOL_ELF, CLIENT, S = sys.argv[2:7]
sys.path.insert(0, str(W / S / 'scripts'))
from r1_devnet_rpc import rpc
CLI = pathlib.Path('/home/dombarker/project-offloads/codex-cx-devnet-rehearse-20261029/NDZ_runtime/extracted/solana-release/bin')
URL = 'http://127.0.0.1:18957'
pub = lambda k: subprocess.check_output([str(CLI / 'solana-keygen'), 'pubkey', str(L / 'keys' / k)], text=True).strip()
art = lambda p: {'path': str(p), 'sha256': hashlib.sha256(pathlib.Path(p).read_bytes()).hexdigest(), 'bytes': pathlib.Path(p).stat().st_size}
c = {'schema': 'aspis.fv.one-tx-spend-config.v1', 'note': 'Aspis freeze rehearsal on a local validator; throwaway keys; new Pool ELF at the address the verifier embeds', 'rpc_url': URL,
     'genesis_hash': rpc(URL, 'getGenesisHash', []), 'payer': pub('payer.json'),
     'programs': {'verifier': pub('verifier.json'), 'pool': POOL, 'registry': '9pWwAcBgwhnkA8JWSA6GvjpYqGzSibLF6GqGH8v6EC9Q'},
     'upload_program': '9DYn3ykkW6JEgYVKst7y7Jd9SqxSjoSNUVTgnGCHWqx5',
     'payer_key': str(L / 'keys/payer.json'), 'key_dir': str(L / 'keys'), 'proof_key_dir': str(L / 'keys'), 'key_namespace': 'FV_local',
     'cli_dir': str(CLI), 'signer': CLIENT,
     'expected_negative_errors': {'cert': {'InstructionError': [0, 'InvalidInstructionData']}, 'node': {'InstructionError': [0, 'InvalidInstructionData']}},
     'release_artifacts': {'devnet_verifier': art(VERIFIER), 'pool': art(POOL_ELF),
                           'registry': art(W / 'devnet/registry.so'), 'upload': art(W / 'devnet/aspis_upload.so')}}
assert c['release_artifacts']['registry']['sha256'].startswith('7ad46f0d') and c['release_artifacts']['upload']['sha256'].startswith('9b2ab3d4')
(L / 'out/FV_local.json').write_text(json.dumps(c, indent=2) + '\n'); print(json.dumps(c['programs'])); print(json.dumps(c['release_artifacts']))
