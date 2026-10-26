#!/usr/bin/env python3
"""Read-only, fail-closed allocation inventory of the pinned Charon source IR.

This is source inspection, not a native allocation certificate. Opaque std
operations, trait dispatch and drop glue are reported explicitly. The LLBC is
an input in a warm extraction cache, never an exported packet artifact.
"""
import argparse
import hashlib
import json
import subprocess
from pathlib import Path

PIN = '8220a6aa2e782c21c365e0a905d61e5427df6729c44c240c99d40d24f6c03856'
REVISION = '4bb3b3f51e16b4525f1d10336e2b0bcbbd775387'


def walk(value):
    if isinstance(value, dict):
        yield value
        for child in value.values():
            yield from walk(child)
    elif isinstance(value, list):
        for child in value:
            yield from walk(child)


def inspect(path):
    raw = path.read_bytes()
    assert hashlib.sha256(raw).hexdigest() == PIN
    document = json.loads(raw)
    assert not document['has_errors']
    data = document['translated']
    functions = data['fun_decls']
    hashed = {}
    for node in walk(data):
        if 'HashConsedValue' in node:
            key, value = node['HashConsedValue']
            assert key not in hashed or hashed[key] == value
            hashed[key] = value

    def resolve(value):
        while isinstance(value, dict):
            if set(value) == {'HashConsedValue'}:
                value = value['HashConsedValue'][1]
            elif set(value) == {'Deduplicated'}:
                value = hashed[value['Deduplicated']]
            else:
                break
        return value

    def name(index):
        return '::'.join(part['Ident'][0] if 'Ident' in part else '<impl>'
                         for part in functions[index]['item_meta']['name'])

    seen, pending, implementations = set(), [0], set()
    absent_methods = set()
    calls = {}
    while pending:
        index = pending.pop()
        if index in seen:
            continue
        seen.add(index)
        calls[index] = []
        for node in walk(functions[index]['body']):
            if 'Call' not in node:
                continue
            callee = node['Call']['call']['func']
            assert set(callee) == {'Regular'}, callee
            callee = callee['Regular']
            calls[index].append(callee)
            kind = callee['kind']
            if 'Regular' in kind.get('Fun', {}):
                pending.append(kind['Fun']['Regular'])
            else:
                assert 'Builtin' in kind.get('Fun', {}) or 'Trait' in kind, kind
            # Include ALL methods of every concrete implementation passed at a
            # reachable call. This over-approximates callbacks; none are omitted
            # merely because a standard helper's body is opaque in this IR.
            for nested in walk(callee['generics']):
                nested = resolve(nested)
                if isinstance(nested, dict) and 'TraitImpl' in nested:
                    impl = nested['TraitImpl']['id']
                    implementations.add(impl)
                    for slot, method in enumerate(data['trait_impls'][impl]['methods']):
                        if method is None:
                            absent_methods.add((impl, slot))
                        else:
                            pending.append(method['skip_binder']['id'])

    rows, boxes, dispatches, opaque = [], [], [], []
    costs, active, zero_loops = {}, set(), []

    def block_cost(block, owner):
        total = 0
        for statement in block['statements']:
            kind = statement['kind']
            if isinstance(kind, str):
                assert kind in {'Return', 'Nop', 'UnwindResume'}, kind
                continue
            assert len(kind) == 1, kind
            tag, value = next(iter(kind.items()))
            if tag == 'Call':
                callee = value['call']['func']['Regular']['kind']
                if 'Regular' in callee.get('Fun', {}):
                    total += function_cost(callee['Fun']['Regular'])
                elif callee.get('Fun', {}).get('Builtin') == 'BoxNew':
                    total += 1
                # Every other builtin and every trait dispatch is an explicit
                # zero-allocation obligation, not a proved native fact.
                if value.get('on_unwind') is not None:
                    assert block_cost(value['on_unwind'], owner) == 0
            elif tag == 'Switch':
                assert len(value) == 1
                switch, fields = next(iter(value.items()))
                if switch == 'If':
                    branches = fields[1:]
                else:
                    assert switch in {'Match', 'SwitchInt'}, switch
                    branches = [arm[1] for arm in fields[1]]
                    if fields[2] is not None:
                        branches.append(fields[2])
                total += max((block_cost(branch, owner) for branch in branches), default=0)
            elif tag == 'Loop':
                # Arbitrarily many iterations are harmless only after checking
                # the complete body (including every nested branch/call) costs0.
                assert block_cost(value, owner) == 0, (owner, statement['id'])
                zero_loops.append([owner, statement['id']])
            else:
                assert tag in {'Assign', 'StorageLive', 'StorageDead', 'Drop',
                               'Break', 'Continue', 'Abort', 'Assert', 'Deinit',
                               'SetDiscriminant'}, tag
                # Drop glue is retained as a separate obligation. Merely
                # omitting its generated body cannot establish allocation0.
        return total

    def function_cost(index):
        if index in costs:
            return costs[index]
        assert index not in active, ('recursive call needs separate proof', index)
        active.add(index)
        body = functions[index]['body']
        cost = block_cost(body['Structured']['body'], index) if isinstance(body, dict) else 0
        active.remove(index)
        costs[index] = cost
        return cost

    for index in sorted(seen):
        function_cost(index)
    for index in sorted(seen):
        function = functions[index]
        body = function['body']
        structured = isinstance(body, dict) and 'Structured' in body
        row = {'id': index, 'name': name(index), 'structured': structured,
               'conditional_box_request_bound': costs[index],
               'source_sha256': hashlib.sha256((function['item_meta'].get('source_text') or '').encode()).hexdigest(),
               'calls': []}
        if not structured:
            assert body == 'Opaque', body
            opaque.append({'id': index, 'name': name(index)})
        for call in calls[index]:
            kind = call['kind']
            row['calls'].append(kind)
            if kind.get('Fun', {}).get('Builtin') == 'BoxNew':
                boxes.append({'function': index, 'name': name(index),
                              'types': call['generics']['types']})
            if 'Trait' in kind:
                dispatches.append({'function': index, 'kind': kind})
        rows.append(row)
    source_pins, source_matches, no_source_text = {}, [], []
    root = Path(__file__).resolve().parents[2]
    for row in rows:
        if not row['name'].startswith(('aspis_statement::', 'aspis_core::')):
            continue
        function = functions[row['id']]
        span = function['item_meta']['span']['data']
        filename = data['files'][span['file_id']]['name']['Local']
        if filename not in source_pins:
            frozen = subprocess.check_output(['git', 'show', REVISION+':'+filename], cwd=root)
            source_pins[filename] = {'sha256': hashlib.sha256(frozen).hexdigest()}
        frozen = subprocess.check_output(['git', 'show', REVISION+':'+filename], cwd=root).decode()
        text = function['item_meta'].get('source_text')
        if text is None:
            no_source_text.append({'function': row['id'], 'file': filename, 'span': span})
        else:
            assert text in frozen, (row['id'], filename)
            source_matches.append(row['id'])
    layouts = []
    for box in boxes:
        assert len(box['types']) == 1
        resolved = resolve(box['types'][0])
        adt = resolved['Adt']['id']['Adt']
        decl = data['type_decls'][adt]
        layouts.append({'function': box['function'], 'type_id': adt,
                        'name': decl['item_meta']['name'][-1]['Ident'][0],
                        'extraction_target_layouts': decl['layout']})
    return {'schema': 'focused-extractor-proof-packet-v1',
            'classification': 'source-inspection-only',
            'llbc_sha256': PIN, 'charon_version': document['charon_version'],
            'release_revision': REVISION, 'release_source_pins': source_pins,
            'exact_source_text_matches': source_matches,
            'no_source_text_functions': no_source_text,
            'box_type_layouts': layouts,
            'root_function': 0, 'reachable_functions': rows,
            'concrete_trait_implementations': sorted(implementations),
            'unrepresented_trait_method_slots': sorted(absent_methods),
            'box_sites': boxes, 'opaque_operations': opaque,
            'trait_dispatches': dispatches,
            'allocation_free_loop_bodies': sorted(set(map(tuple, zero_loops))),
            'conditional_raw_decoder_box_bound': costs[0],
            'bound_conditions': ['all reported opaque operations allocate0',
                                 'all reported trait dispatches allocate0',
                                 'all non-BoxNew builtins allocate0',
                                 'all drop glue allocates0',
                                 'source IR control flow faithfully represents execution'],
            'includes_unwind_paths': True,
            'native_allocation_bound_proved': False,
            'enclosing_premises_removed': 0}


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('llbc', type=Path)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    report = inspect(args.llbc)
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps({'reachable_functions': len(report['reachable_functions']),
                      'box_sites': report['box_sites'],
                      'opaque_operations': report['opaque_operations'],
                      'trait_dispatch_count': len(report['trait_dispatches'])}, indent=2))
