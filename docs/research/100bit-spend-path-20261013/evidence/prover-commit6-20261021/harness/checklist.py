#!/usr/bin/env python3
import json
from pathlib import Path
R=Path('docs/research/v8-r0-zk-20261009/r1p-final')
E=Path(__file__).resolve().parent.parent
old=(R/'PROVER-COMMIT5-20261021.md').read_text()
before=old.split('## After (verbatim; all nine complete rows retained open):')[1].split('```text\n')[1].split('```')[0]
rows=before.strip().splitlines();assert len(rows)==9
after=rows[:6]+[
'| R_commit_quotient_fibres, cF | Equal successful fibres on the H1 quotient; measure-preserving completion is proved. The explicit sequential wordsE decoder has a derived fibre constant and a successful input; the actual source/caller/order/field-image equation remains open. |',
'| R_commit_exhaustion | Every tapeOf failure must imply one of the actual two 16-try little-endian stream-exhaustion events. Quotient packing adds no failures; the source caller/cursor law and exact wordsE-to-Exhausted classification remain open. |',
'| R_commit_counter₁/₂, R_commit_stream₁/₂, R_commit_cell_count, R_commit_blocks₁/₂ | All coordinate-model count, canonical stream/block and counter bounds are proved. The universal shipped caller/read-completeness instance remains open; model cardinalities do not establish source coverage. |']
result=dict(before_verbatim=before,after_verbatim='\n'.join(after)+'\n',complete_source_rows_closed=[],
 subobligations_closed=['release quotient-law replacement with unchanged conclusion','full-fibre implication and strictness','full constructed commitment-observable transport','M31 and five-family quotient carriers','sequential model decoder equal fibres with derived cF','coordinate-model counts and budgets','packing failure iff stream decoder failure'],
 remaining=['universal source caller/pre-balance/order/field-image identity','source cursor and exact RExh classification','complete source commitment read coverage'])
(E/'checklist-before-after.json').write_text(json.dumps(result,indent=2)+'\n')
p=R/'PROVER-COMMIT6-20261021.md'
with p.open('a') as f:
 f.write('\n## Before (verbatim)\n\n```text\n'+before+'```\n\n## After (verbatim; nine complete source rows remain open)\n\n```text\n'+result['after_verbatim']+'```\n')
