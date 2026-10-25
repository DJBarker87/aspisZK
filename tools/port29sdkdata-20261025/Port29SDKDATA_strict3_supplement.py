#!/usr/bin/env python3
"""Source-only release/worklist supplement, no compiler invocation."""
import collections,json,subprocess,time
from pathlib import Path
from Port29SDKDATA_diagnostic import E,pin,write
from Port29SDKDATA_strict3 import NEW,PREP
start=time.monotonic();p=json.loads(PREP.read_text());o=Path(p['directory']);a=json.loads((E/'Port29SDKDATA_Strict-v3-final-audit.json').read_text())
gp=next(x['path'] for x in a['artifacts'] if x['path'].endswith('cross-origin-edges-final.jsonl'));known=set();deps=set()
with Path(gp).open() as f:
 for line in f:
  r=json.loads(line)
  if r['side'] in ['CURRENT','CURRENT-INCREMENTAL']:known.add(r['name']);deps.update(r['dependencies'])
fragments=json.loads((NEW/'audit-input.json').read_text())['transport'];counts=collections.Counter(m for m,p in fragments)
assert len(fragments)==1428 and len(counts)==1375 and sum(v-1 for v in counts.values())==53
assert len(known)==28506 and not deps-known
sources=[]
for n in ['S8OwnedP6/Types.lean','S8OwnedP6/Funs.lean','OraclePortCompactDraft.lean','S2W_FirstOccurrence.lean','S2W_OuterOccurrences.lean']:
 path='docs/research/100bit-spend-path-20261013/lean/'+n
 b=subprocess.check_output(['git','show','904745b496:'+path]);import hashlib
 sources.append(dict(revision='904745b496c1eb84871aacd83b8f9d42f0762613',path=path,bytes=len(b),sha256=hashlib.sha256(b).hexdigest()))
write(E/'Port29SDKDATA_Strict-v3-release-supplement.json',dict(current_name_edge_graph=dict(unique_names=len(known),missing_dependencies=sorted(deps-known),logical_kernel_selection_closed=False,assessment='First-observation baseline edges reused, all141 new raw modules independently inspected;43 duplicate-origin assertions remain qualified alpha data'),
 fragments=dict(raw_paths=len(fragments),module_labels=len(counts),same_label_additions=sum(v-1 for v in counts.values()),overwritten_baseline_paths=0),
 immutable_source_prerequisites=sources,
 missing_factor_original_counterparts=['AspisR1.S2W_D189Entry.first_disjoint._proof_1_1','AspisR1.S2W_D189Wrappers.first.match_3'],
 next_consumer='After separately authorized acquisition of36 missing bodies, preserve13 conflicts/45 strict representation differences; execute43 CURRENT duplicate and new variant worklists, reject project axioms/unsafe/partial seeds, kernel-reconstruct chosen closure and audit concrete originalFirst/first_eq_original and original SDK accepted returned tuple/cuts. Obtain explicit raw delta for three acee source-selected-cut modules before stronger endpoint. No FullForest/equality/input-retention/semanticModel premise introduced.',
 new_assumptions=0,axioms='N/A: source/data only',source=pin(__file__),wall_seconds=time.monotonic()-start,exit_status=0))
print('CURRENT graph28506 names/0 gaps;1428 fragments/1375 labels/53 additions; strict coherent selection remains OPEN')
