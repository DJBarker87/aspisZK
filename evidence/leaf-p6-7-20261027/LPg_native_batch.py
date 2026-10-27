from pathlib import Path
import json,subprocess
E=Path(__file__).resolve().parent
rows=[('fast_pairing::canonical::LPg_dot::LPg_'+n+'_contract') for n in ['reduce','add','qadd']]+['verifier::LPg_verifier::LPg_echeck0','verifier::LPg_verifier::LPg_echeck1','compact::LPg_compact::LPg_check_step','r1_wire::LPg_r1_wire::LPg_validate_step','compact::LPg_compact::LPg_expand_low','compact::LPg_compact::LPg_expand_high']
for i,target in enumerate(rows,3):
 a=f'LPg_K{i:03}';subprocess.run(['python3',str(E/'LPg_attempt.py'),a,'kani',target],check=True)
 r=json.loads((E/a/'receipt.json').read_text())
 if r['exit_status'] and 'timed out' not in (E/a/'stdout.log').read_text():raise SystemExit('STOP compile/counterexample '+a)
