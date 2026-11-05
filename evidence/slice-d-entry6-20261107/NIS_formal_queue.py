from NIS_formal import *
for i,m in enumerate(json.loads((E/'NIS_RETARGET.json').read_text())['order'],1):
    a=f'NIS_L{i:03}'
    if (E/a/'receipt.json').exists():
        assert json.loads((E/a/'receipt.json').read_text())['exit_status']==0
        continue
    rc=run(a,'lean',m)
    if rc['exit_status']:sys.exit(rc['exit_status'])
print('Canonical focused modules and combined import PASS',flush=True)
