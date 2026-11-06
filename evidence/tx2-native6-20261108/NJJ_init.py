from pathlib import Path
import json,hashlib
E=Path('evidence/tx2-native6-20261108');E.mkdir(exist_ok=True)
(E/'NJJ_HANDOFF.md').write_text('''# NJJ early handoff

TX2:065 OPEN; target not yet established. Work in progress on ruling (au) dictionary elimination and library models. No row promoted. No new trust item. Merkle TX2:053 belongs to NJE_; finish TX2:115 belongs to NJF_; neither is assumed CLOSED.

Workspace: /home/dombarker/project-offloads/codex-cx-tx2-native6-20261108. CARGO_TARGET_DIR: workspace/NJJ_target. Seed predecessor retained export first, then NJC_PATHS.json read-only order. Budget: 80 Kani, 100 Lean, 1 extraction. Strict reservation admission and one capped scope at a time; no timeout/cap increases. Source frozen at 4bb3b3f51e16b4525f1d10336e2b0bcbbd775387. No shipped changes or key operations.

Next: classify every Ops field and M01–M13; pin inputs and seed; compile focused library facts and native cuts; print dictionary-free root with precise sibling dependencies; run at most two combined audits. Credit waits for ledger gate.
''')
p=Path('evidence/tx2-native5-20261107/NJC_setup.py').read_text().replace('codex-cx-tx2-native5-20261107','codex-cx-tx2-native6-20261108').replace('NJC','NJJ').replace('NIY_exports_20261107','NJC_exports_20261107')
(E/'NJJ_setup.py').write_text(p)
paths=json.loads(Path('evidence/tx2-native5-20261107/NJC_PATHS.json').read_text())
paths.insert(0,'/home/dombarker/project-offloads/codex-cx-tx2-native6-20261108/NJJ_objects')
paths.insert(1,'/home/dombarker/project-offloads/codex-cx-slice-d-prepared-cache-20261104/NJJ_seed_20261107')
(E/'NJJ_PATHS.json').write_text(json.dumps(paths,indent=2)+'\n')
inputs=['/Users/dominic/ZK/AGENTS.md','/private/tmp/claude-501/-Users-dominic-ZK/4dec4925-8c43-447e-9333-6147c1c7863b/scratchpad/local-lean.txt','/private/tmp/claude-501/-Users-dominic-ZK/4dec4925-8c43-447e-9333-6147c1c7863b/scratchpad/r1p-common.txt']
inputs+= [str(p) for p in Path('docs/research/100bit-spend-path-20261013/design').glob('*.md') if p.name in ['S2-OWNERSHIP-HANDOFF-20261023.md','S2-LEAD-PLAN-20261023.md','C3-BIN-20261021.md','VERTICAL-SLICES-20261029.md','SECURITY-CONTRACT-20261021.md']]
(E/'NJJ_RULE_PINS.json').write_text(json.dumps({s:hashlib.sha256(Path(s).read_bytes()).hexdigest() for s in inputs},indent=2)+'\n')
