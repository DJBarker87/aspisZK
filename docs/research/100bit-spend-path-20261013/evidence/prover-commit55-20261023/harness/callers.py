from pathlib import Path
import subprocess,sys
H=Path('/home/dombarker/project-offloads/codex-cx-prover-commit55-20261023')
checks=[('constructors-v4','proofs::constructors'),('semantic-challenges-v2','proofs::semantic_challenges'),('field-projections-v2','proofs::projections'),('power-transition-v2','power::transition')]
checks += [(f'{ty}-channel-{s}-v3',f'fixed_channels::{ty}_channel_{s}') for ty in ['m','q'] for s in range(4)]
for name,harness in checks:
 print(name,flush=True)
 rc=subprocess.run(['python3',str(H/'harness/kani-caller.py'),name,harness]).returncode
 if rc:sys.exit(rc)
