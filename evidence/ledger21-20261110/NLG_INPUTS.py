from pathlib import Path
import hashlib,json,subprocess
E=Path(__file__).resolve().parent
paths=['/Users/dominic/ZK/AGENTS.md','/private/tmp/claude-501/-Users-dominic-ZK/4dec4925-8c43-447e-9333-6147c1c7863b/scratchpad/r1p-common.txt','/private/tmp/claude-501/-Users-dominic-ZK/4dec4925-8c43-447e-9333-6147c1c7863b/scratchpad/local-lean.txt']
paths += ['docs/research/100bit-spend-path-20261013/'+p for p in ['design/S2-OWNERSHIP-HANDOFF-20261023.md','design/S2-LEAD-PLAN-20261023.md','evidence/s2-lead-20261023/DIAGNOSIS.md','design/C3-BIN-20261021.md','lean/S2LeadInterface.lean','design/SECURITY-CONTRACT-20261021.md','design/VERTICAL-SLICES-20261029.md','design/VERTICAL-SLICES-20261029.json']]
paths += ['evidence/'+p for p in ['sound-int2-20261025/HANDOFF.md','ledger20-20261109/NKW_HANDOFF.md','ledger20-20261109/NKW_LEDGER_DELTA.json','ledger20-20261109/NKW_PHYSICAL.md','ledger20-20261109/NKW_LEDGER.json.xz','ledger20-20261109/NKW_REMAINING.md','native-ledger3-20261029/NDT_LEDGER.md','native-ledger3-20261029/NDT_LEDGER.json','pool-inventory2-20261109/NKZ_INVENTORY.json','pool-inventory2-20261109/NKZ_OBLIGATIONS.md','pool-inventory2-20261109/NKZ_DIFF.md']]
rows=[]
for n in paths:
 p=Path(n);b=p.read_bytes()if p.exists()else subprocess.check_output(['git','show','HEAD:'+n]);rows.append(dict(path=n,sha256=hashlib.sha256(b).hexdigest(),bytes=len(b)))
(E/'NLG_INPUTS.json').write_text(json.dumps(dict(read_only_inputs=rows,rulings={'bd':'Fold-first ONE State/event sequence; intermediate conditional lemmas earn no row credit; roots substitute all child packets','be':'Parent defines full typed RowSpec if missing, child proves exactly it; AccountInfo wrapper over admitted RefCell semantics reviewed under std, no new row; NLF shared support'},budget=dict(Lean_link_audit=40,Kani=0,extraction=0)),indent=1)+'\n');print('Required input/ruling pins recorded')
