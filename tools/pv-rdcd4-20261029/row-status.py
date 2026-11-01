"""Record a conservative row disposition; restoration requires its own gate."""
from pathlib import Path
import json,sys,subprocess
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-rdcd4-20261029';n=int(sys.argv[1]);reason=sys.argv[2]
assert n in [220,237,236,233,197]
x=json.load(open(R/f'evidence/pv-rdcd3-20261028/rows/V{n}.json'))
x.update(status='SUSPENDED',rdcd4_status='in progress; no new whole-row credit',reason=reason,next_deliverable=reason,source_revision=subprocess.check_output(['git','rev-parse','HEAD'],cwd=R,text=True).strip(),endpoint_premises_removed=[],endpoint_premises_added=[],endpoint_premises_changed=[])
(E/f'rows/V{n}.json').write_text(json.dumps(x,indent=2)+'\n')
(E/f'rows/V{n}.md').write_text(f'''# V{n} — SUSPENDED / D

{reason}

Before and after: the complete deployed source-to-reference Result law remains
an obligation, with the same inputs, quantifiers, errors and conclusion.
No endpoint premise was removed, added or changed. Compiler V370/D381/D386,
E1/E2, native RunJoin/world/physical observer, client route, L1/L2/L3 and T remain.
''')
