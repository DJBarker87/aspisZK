"""Create an unverified diagnostic selection; never change declaration rows."""
import collections, hashlib, json, pathlib

HERE = pathlib.Path(__file__).resolve().parent
BASE = HERE.parent
source = BASE / 'body-comparison/input/R438GenericClosureDispatch.llbc'
edge_path = BASE / 'declaration-groups/dependency-edges.json'
summary_path = BASE / 'declaration-groups/dependency-summary.json'
sha = lambda data: hashlib.sha256(data).hexdigest()
original_bytes = source.read_bytes()
assert sha(original_bytes) == '76eefed780e23eb3243413b913e935dc7a9b661bceeb0fc0346668621ab07fb6'
summary_bytes = summary_path.read_bytes()
edge_bytes = edge_path.read_bytes()
summary = json.loads(summary_bytes)
edges = json.loads(edge_bytes)
assert summary['input_sha256'] == sha(original_bytes)
assert summary['roots'] == [['Fun', 284], ['TraitImpl', 47]]
roots = {('Fun', 284), ('TraitImpl', 47)}
graph = collections.defaultdict(set)
for edge in edges:
    if edge['available_row'] and not edge['pinned_parent_suppressed']:
        graph[tuple(edge['from'])].add(tuple(edge['to']))
reachable = set(roots)
queue = list(roots)
while queue:
    for target in graph[queue.pop()]:
        if target not in reachable:
            reachable.add(target)
            queue.append(target)
assert len(reachable) == summary['reachable_node_count'] == 40
text = original_bytes.decode('utf-8')
original = json.loads(text)
assert original['has_errors'] is False
groups = original['translated']['ordered_decls']
selected = []
members = set()
for group in groups:
    assert len(group) == 1
    kind, inner = next(iter(group.items()))
    assert list(inner) == ['NonRec']  # This frozen input has singleton groups.
    item = (kind, inner['NonRec'])
    if item in reachable:
        selected.append(group)
        members.add(item)
assert members == reachable
assert len(selected) == 40
assert ('Type', 70) not in members
assert roots <= members
assert text.count('"ordered_decls":') == 1
start = text.index('"ordered_decls":') + len('"ordered_decls":')
decoded, end = json.JSONDecoder().raw_decode(text, start)
assert decoded == groups
prefix = text[:start].encode('utf-8')
suffix = text[end:].encode('utf-8')
selection = json.dumps(selected, separators=(',', ':')).encode('utf-8')
projected_bytes = prefix + selection + suffix
projected = json.loads(projected_bytes)
restored = json.loads(projected_bytes)
restored['translated']['ordered_decls'] = groups
assert restored == original
assert projected['translated']['ordered_decls'] == selected
assert projected_bytes[:len(prefix)] == original_bytes[:len(prefix)]
assert projected_bytes[-len(suffix):] == original_bytes[-len(suffix):]
target = HERE / 'R439GenericGammaSelection.llbc'
assert not target.exists(), 'preserve prior diagnostic input'
target.write_bytes(projected_bytes)
(HERE / 'dependency-edges.snapshot.json').write_bytes(edge_bytes)
(HERE / 'dependency-summary.snapshot.json').write_bytes(summary_bytes)
receipt = {
    'status': 'UNVERIFIED_DIAGNOSTIC_INPUT_NOT_AUTHORIZED_FOR_LAUNCH',
    'source_path': str(source), 'source_sha256': sha(original_bytes),
    'target': str(target), 'target_sha256': sha(projected_bytes),
    'generator_sha256': sha(pathlib.Path(__file__).read_bytes()),
    'edge_snapshot_sha256': sha(edge_bytes), 'summary_snapshot_sha256': sha(summary_bytes),
    'original_groups': len(groups), 'selected_groups': len(selected),
    'selected_members': sorted(map(list, members)),
    'only_changed_json_field': 'translated.ordered_decls',
    'prefix_bytes': len(prefix), 'prefix_sha256': sha(prefix),
    'suffix_bytes': len(suffix), 'suffix_sha256': sha(suffix),
    'all_other_raw_bytes_preserved': True,
    'full_declaration_tables_and_hash_cons_records_preserved': True,
    'original_absent_references_preserved': summary['missing_references'],
    'boundary': 'Extraction selection diagnostic only. Dependency classification awaits independent schema audit. No source execution, borrow, callback chronology or security proof.',
    'next_gate': 'Independent schema-specific dependency audit and lead runner review before any translation launch.',
}
(HERE / 'projection-receipt.json').write_text(json.dumps(receipt, indent=2) + '\n')
print(json.dumps({key: receipt[key] for key in ('status', 'target_sha256', 'selected_groups', 'only_changed_json_field')}))
