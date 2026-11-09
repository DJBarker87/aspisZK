#!/usr/bin/env python3
"""PCO_finalize_partition.py: PCO_partition.py output + shadow candidates + pilot corrections -> PCO_PARTITION.json.
Usage: PCO_finalize_partition.py l30_partition.json shadow.json OUT.json
Corrections applied (each also in PCO_CLASSIFICATIONS.json):
  PILOT-1  AspisR1WideToBytesSource.Funs: a_identical -> c1. The pilot proved by Lean (PCO_L008, control PCO_L007) that the compiled gate
           module is the hand-adapted source, so three of its four reached definitions are not equal to a fresh frozen emission.
Everything else is the unmodified PRV method at the ledger30 base."""
import json, sys, collections
part = json.load(open(sys.argv[1])); shadow = json.load(open(sys.argv[2]))
mods = part['modules']
for m, s in shadow.items():
    mods[m]['shadow_candidates'] = s['shadows']
    mods[m]['compiled_source_ambiguous'] = True
c = mods['AspisR1WideToBytesSource.Funs']
c['pilot_correction'] = dict(old_group='a', old_subgroup=c['subgroup'], new_group='c', new_subgroup='c1_extraction_exists_equality_needed',
    reason='PCO pilot: compiled gate module is generated-adapted/Funs.lean (P6ToBytes.StdModel iterator/zip externals); fresh frozen emission PCO_E001 matches only to_limbs by rfl; to_le_bytes_loop(.body), to_le_bytes need transport (PCO_L008, control PCO_L007).')
c['group'] = 'c'; c['subgroup'] = 'c1_extraction_exists_equality_needed'
for b in part['blobs']:
    if b['module'] == 'AspisR1WideToBytesSource.Funs' and b['group'] == 'a': b['group'] = 'c'; b['subgroup'] = 'c1_extraction_exists_equality_needed'; b['pilot_correction'] = True
S = part['summary']
S['module_groups'] = dict(collections.Counter(r['group'] for r in mods.values())); S['module_subgroups'] = dict(collections.Counter(r['subgroup'] for r in mods.values()))
S['blob_groups'] = dict(collections.Counter(x['group'] for x in part['blobs'])); S['blob_subgroups'] = dict(collections.Counter(x['subgroup'] for x in part['blobs']))
def rows_of(pred): return sorted(set(x for r in mods.values() if pred(r) for x in r['rows']))
Rc = rows_of(lambda r: r['group'] == 'c'); Rb3 = rows_of(lambda r: r['subgroup'] == 'b3_source_not_found'); Rb2 = rows_of(lambda r: r['subgroup'].startswith('b2'))
Rap = rows_of(lambda r: r['subgroup'] == 'a_pending_live_version_is_receipted_or_copy')
S['rows']['c'] = len(Rc); S['rows']['c_or_b_unlinked'] = len(set(Rc) | set(Rb2) | set(Rb3)); S['rows']['c_or_b_unlinked_or_a_pending'] = len(set(Rc) | set(Rb2) | set(Rb3) | set(Rap))
part['rows_affected_c'] = Rc; part['rows_affected_c_or_b_unlinked'] = sorted(set(Rc) | set(Rb2) | set(Rb3)); part['rows_affected_c_or_b_unlinked_or_a_pending'] = sorted(set(Rc) | set(Rb2) | set(Rb3) | set(Rap))
S['shadow_candidate_modules'] = sorted(shadow)
part['basis']['recompute'] = 'PCO_partition.py (port of PRV_scripts) at research 6ce07a6a593 with ledger30 NNN_ files; see PCO_CLASSIFICATIONS.json for every substitution; shadow candidates by PCO_shadow.py'
part['schema'] = 1
json.dump(part, open(sys.argv[3], 'w'), indent=0)
print(json.dumps(S['module_groups']), json.dumps(S['rows']))
