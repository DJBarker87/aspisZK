#!/usr/bin/env python3
"""Aspis freeze devnet run: write the run config (schema of the earlier one-transaction run, read by the
unchanged FV_preflight.py, FV_spend.py and FV_cleanup.py).
usage: ASPIS_config.py <run-dir> <verifier-program-id> <pool-program-id> <source-commit> <out.json>
The four ELFs are read from <run-dir>/artifacts (verifier.so, pool.so, registry.so, aspis_upload.so)."""
import hashlib, json, pathlib, sys
R = pathlib.Path(sys.argv[1]); verifier, pool, commit, out = sys.argv[2:6]
art = lambda n: {'path': str(R / 'artifacts' / n), 'sha256': hashlib.sha256((R / 'artifacts' / n).read_bytes()).hexdigest(), 'bytes': (R / 'artifacts' / n).stat().st_size}
c = {'schema': 'aspis.fv.one-tx-spend-config.v1',
     'note': f'Aspis one-transaction verifier, frozen source {commit}: devnet run with the new Pool program. Test deployment; no security claim is made by this run.',
     'rpc_url': 'https://api.devnet.solana.com', 'genesis_hash': 'EtWTRABZaYq6iMfeYKouRu166VU2xqa1wcaWoxPkrZBG',
     'payer': 'CVZJcAv97von8njTJSyLVQ9X33NAKQYbEXFKnAYvst9t',
     'programs': {'verifier': verifier, 'pool': pool, 'registry': '9pWwAcBgwhnkA8JWSA6GvjpYqGzSibLF6GqGH8v6EC9Q'},
     'upload_program': '9DYn3ykkW6JEgYVKst7y7Jd9SqxSjoSNUVTgnGCHWqx5',
     'payer_key': '/Users/dominic/.config/solana/aspis-deploy/devnet-payer-20261029.json',
     'key_dir': '/Users/dominic/.config/solana/aspis-deploy/ASPIS_onetx-20261112',
     'proof_key_dir': '/Users/dominic/.config/solana/aspis-deploy/ASPIS_onetx-20261112',
     'key_namespace': 'ASPIS_devnet', 'cli_dir': '/opt/aspis/cli', 'signer': '/opt/aspis/devnet_spend', 'uploads_together': True,
     'expected_negative_errors': {'cert': {'InstructionError': [0, 'InvalidInstructionData']}, 'node': {'InstructionError': [0, 'InvalidInstructionData']}},
     # Pinned from the rehearsals on a local validator (host runs frzlocal2 and frzlocal3).
     'expected_redirect_errors': {'redirect-both': {'InstructionError': [0, 'InvalidInstructionData']},
                                  'redirect-account': {'InstructionError': [0, {'Custom': 1095966770}]},
                                  'redirect-request': {'InstructionError': [0, {'Custom': 1095966770}]}},
     'release_artifacts': {'devnet_verifier': art('verifier.so'), 'pool': art('pool.so'), 'registry': art('registry.so'), 'upload': art('aspis_upload.so')}}
assert c['release_artifacts']['registry']['sha256'].startswith('7ad46f0d') and c['release_artifacts']['upload']['sha256'].startswith('9b2ab3d4')
pathlib.Path(out).write_text(json.dumps(c, indent=1) + '\n'); print(json.dumps(c['release_artifacts'], indent=1))
