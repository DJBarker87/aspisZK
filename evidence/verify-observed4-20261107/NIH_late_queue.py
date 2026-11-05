from pathlib import Path
import subprocess,json,sys
from NIH_config import write
E=Path(__file__).resolve().parent
jobs=[(67, 'NIH_internal_native::NIH_packed_group', False), (68, 'NIH_internal_native::NIH_packed_group', True), (69, 'NIH_internal_native::NIH_packed_sum', False), (70, 'NIH_internal_native::NIH_packed_sum', True), (71, 'NIH_internal_native::NIH_packed_map', False), (72, 'NIH_internal_native::NIH_packed_map', True), (73, 'NIH_internal_native::NIH_round_prefix', False), (74, 'NIH_internal_native::NIH_round_prefix', True), (75, 'NIH_internal_native::NIH_round_tail', False), (76, 'NIH_internal_native::NIH_round_tail', True), (77, 'NIH_internal_native::NIH_lazy_matrix', False), (78, 'NIH_internal_native::NIH_lazy_matrix', True), (79, 'NIH_internal_native::NIH_lazy_row', False), (80, 'NIH_internal_native::NIH_lazy_row', True), (81, 'NIH_internal_native::NIH_lazy_group', False), (82, 'NIH_internal_native::NIH_lazy_group', True), (83, 'NIH_internal_native::NIH_lazy_sum', False), (84, 'NIH_internal_native::NIH_lazy_sum', True), (85, 'NIH_internal_native::NIH_lazy_tail', False), (86, 'NIH_internal_native::NIH_lazy_tail', True), (87, 'NIH_internal_native::NIH_full_qm_prefix', False), (88, 'NIH_internal_native::NIH_full_qm_prefix', True), (89, 'NIH_internal_native::NIH_full_m31_prefix', False), (90, 'NIH_internal_native::NIH_full_m31_prefix', True), (91, 'NIH_internal_native::NIH_full_lazy_tail', False), (92, 'NIH_internal_native::NIH_full_lazy_tail', True), (93, 'NIH_internal_native::NIH_full_packed_tail', False), (94, 'NIH_internal_native::NIH_full_packed_tail', True)]
for n,name,negative in jobs:
 a=f'NIH_K{n:03}';write(a,'kani','state_only_poseidon::'+name,'--cfg NIH_invert' if negative else '')
 with (E/(a+'-client.log')).open('w') as log:r=subprocess.run([sys.executable,str(E/'NIH_run.py'),a],stdout=log,stderr=subprocess.STDOUT)
 p=E/a/'receipt.json'
 if not p.exists():print(a,'missing receipt STOP',flush=True);sys.exit(1)
 rc=json.loads(p.read_text());raw=(E/a/'stdout.log').read_text();expected=r.returncode==(1 if negative else 0) and ('VERIFICATION:- FAILED' if negative else 'VERIFICATION:- SUCCESSFUL') in raw
 print(json.dumps(dict(attempt=a,negative=negative,exit=r.returncode,expected=expected,wall=rc['wall_seconds'],rss=rc['peak_rss_kib'])),flush=True)
 if not expected:sys.exit(1)
