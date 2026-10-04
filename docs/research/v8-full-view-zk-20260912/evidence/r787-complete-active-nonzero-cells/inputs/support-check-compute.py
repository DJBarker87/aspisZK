#!/usr/bin/env python3
"""Index-only support comparison for the saved R769 active block.
No field arithmetic, rank computation, or Lean/source-cell correspondence claim.
"""
import csv, hashlib, json
from pathlib import Path

ROOT = Path('docs/research/v8-full-view-zk-20260912/evidence/r769-point1-selected-entries')
RAW = ROOT / 'inputs/matrix.raw.tsv'
MAP = ROOT / 'lead-mapping-check.json'
SUMMARY = Path('.r21-scratch/r778-active-matrix-sparsity-summary.json')
OUT = Path('.r21-scratch/r787-selected-support-preflight/support-check.json')

def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def index_loop(fuel, row, bit):
    if fuel == 0: return None
    if row & (1 << bit):
        nxt = row ^ (1 << bit)
        rest = index_loop(fuel - 1, nxt, bit + 1)
        return None if rest is None else [(nxt, bit + 1)] + rest
    return [(row | (1 << bit), bit)]
def index_targets(j):
    edges = index_loop(10, j, 0)
    return [] if edges is None else [target for target, _ in edges]

def even_support(j, r, targets):
    return r // 2 == j or (r % 2 == 0 and r // 2 in targets[j])
def odd_support(j, r, targets):
    if r // 2 == j: return True
    if r % 2 == 0:
        return r // 2 in {v for u in targets[j] for v in targets[u]}
    return r // 2 in targets[j]
def pair_support(d, s, r, targets):
    return even_support(2*d, r, targets) or (
        even_support(2*d+1, r, targets) if s == 1 else odd_support(2*d+s//2, r, targets)
    )

raw_rows = list(csv.reader(RAW.open(), delimiter='\t'))
assert raw_rows[0] == ['rows=222 columns=242']
assert len(raw_rows) == 243 + 222
raw_headers = {}
for row in raw_rows[1:243]:
    assert len(row) == 4 and row[0] == 'column'
    raw_headers[int(row[1])] = (int(row[2]), int(row[3]) - 1)
assert set(raw_headers) == set(range(242))
data = {}
for row in raw_rows[243:]:
    assert len(row) == 245 and row[0] == 'row'
    data[int(row[1])] = row
assert set(data) == set(range(222))
summary = json.loads(SUMMARY.read_text())
rowcodes = [x['source_rowcode'] for x in summary['raw_row_slot_to_label_and_source_rowcode']]
assert len(rowcodes) == 214 and all(96 <= r < 1024 for r in rowcodes)
columns = json.loads(MAP.read_text())['exact_selected_columns']
assert len(columns) == 222 and len(set(columns)) == 222 and all(c in raw_headers for c in columns)
targets = {j: index_targets(j) for j in range(512)}

support_positions = []
raw_nonzero_positions = []
inside_cancelled = []
outside_nonzero = []
row_summary = []
for rs, code in enumerate(rowcodes):
    support_cols = []
    nonzero_cols = []
    for cp, rawcol in enumerate(columns):
        d, s = raw_headers[rawcol]
        assert 0 <= d < 255 and 0 <= s < 3
        supported = pair_support(d, s, code, targets)
        limbs = [int(v) for v in data[rs][3 + rawcol].split(',')]
        assert len(limbs) == 4
        nonzero = any(v != 0 for v in limbs)
        if supported:
            support_cols.append(cp)
            support_positions.append({'row_slot':rs,'row_code':code,'column_position':cp,
                                      'raw_column':rawcol,'d':d,'s':s})
            if not nonzero:
                inside_cancelled.append({'row_slot':rs,'row_code':code,'column_position':cp,
                                         'raw_column':rawcol,'d':d,'s':s})
        if nonzero:
            nonzero_cols.append(cp)
            raw_nonzero_positions.append({'row_slot':rs,'row_code':code,'column_position':cp,
                                          'raw_column':rawcol,'d':d,'s':s,'limbs':limbs})
            if not supported:
                outside_nonzero.append({'row_slot':rs,'row_code':code,'column_position':cp,
                                        'raw_column':rawcol,'d':d,'s':s,'limbs':limbs})
    row_summary.append({'row_slot':rs,'row_code':code,'support_columns':support_cols,
                        'raw_nonzero_columns':nonzero_cols})
assert len(support_positions) == 700
assert len(raw_nonzero_positions) == 700
assert not inside_cancelled and not outside_nonzero
assert [(x['row_slot'],x['column_position']) for x in support_positions] == \
       [(x['row_slot'],x['column_position']) for x in raw_nonzero_positions]

obj = {
  'scope':'metadata-only support comparison; no field arithmetic, rank, Lean proof, or source-cell binding',
  'input_sha256': {'raw_matrix':sha(RAW),'mapping_check':sha(MAP),'sparsity_summary':sha(SUMMARY)},
  'schedule': {'source':'AspisV8R17.IndexSchedule.indexLoop; fuel=10, initial bit=0',
               'targets_sha256':hashlib.sha256(json.dumps(targets,sort_keys=True,separators=(',',':')).encode()).hexdigest()},
  'support_definition':'evenUnitSupport(2*d,r) OR (s=1 ? evenUnitSupport(2*d+1,r) : oddUnitSupport(2*d+s/2,r)); R787PairSupportZero',
  'selected_raw_columns':columns,
  'selected_headers_d_s':[[raw_headers[c][0],raw_headers[c][1]] for c in columns],
  'counts': {'rows':214,'columns':222,'cells':214*222,'support_positive':len(support_positions),
             'literal_nonzero':len(raw_nonzero_positions),'support_positive_but_literal_zero':len(inside_cancelled),
             'outside_support_but_literal_nonzero':len(outside_nonzero),
             'literal_zero_outside_support':214*222-len(support_positions)},
  'support_positions':support_positions,
  'literal_nonzero_positions':raw_nonzero_positions,
  'rows':row_summary,
  'mapping_boundary':'Rows are summary slots labeled by source row code; columns use raw TSV (d,slot-1) headers. Mapping every row/column to the Lean R746 chosenSourceMatrix remains unresolved; this file does not assert raw matrix cells equal Lean source chords.'
}
OUT.write_text(json.dumps(obj,indent=2,sort_keys=True)+'\n')
print(json.dumps(obj['counts'],sort_keys=True))
print('support-check sha256',sha(OUT))
