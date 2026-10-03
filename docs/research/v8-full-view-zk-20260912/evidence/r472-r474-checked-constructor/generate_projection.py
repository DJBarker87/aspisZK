"""Fail-closed syntactic projection; not a Rust/LLBC semantics proof."""
import argparse, hashlib, json, pathlib

parser = argparse.ArgumentParser()
parser.add_argument('source', type=pathlib.Path)
parser.add_argument('target', type=pathlib.Path)
parser.add_argument('--check', action='store_true')
args = parser.parse_args()
raw = args.source.read_bytes()
source_hash = hashlib.sha256(raw).hexdigest()
assert source_hash == '96135e91c71f93dcd3aeec7b693eb737e7cf05027456ca973242cf2586088c48'
tree = json.loads(raw)['translated']
types = {}
def scan(value):
    if isinstance(value, dict):
        if 'HashConsedValue' in value:
            ident, body = value['HashConsedValue']
            assert ident not in types or types[ident] == body
            types[ident] = body
        for child in value.values(): scan(child)
    elif isinstance(value, list):
        for child in value: scan(child)
scan(tree)
def resolve(value):
    if isinstance(value, dict):
        if 'HashConsedValue' in value: return resolve(value['HashConsedValue'][1])
        if 'Deduplicated' in value: return resolve(types[value['Deduplicated']])
        return {k: resolve(v) for k, v in value.items()}
    if isinstance(value, list): return [resolve(v) for v in value]
    return value
empty = {'regions': [], 'types': [], 'const_generics': [], 'trait_refs': []}
qm31 = {'Adt': {'id': {'Adt': 2}, 'generics': empty}}
slice_qm31 = {'Slice': qm31}
assert resolve(types[544]) == qm31
assert resolve(types[545]) == slice_qm31
for ident, pointee, size in [(58, qm31, 8), (69, slice_qm31, 16)]:
    decl = tree['type_decls'][ident]
    assert len(decl['kind']['Struct']) == 1
    field = decl['kind']['Struct'][0]
    assert field['name'] == 'pointer'
    assert resolve(field['ty']) == {'Pattern': [{'RawPtr': [pointee, 'Shared']}, 'NotNull']}
    layout, = [r['value'] for r in decl['layout'] if r['key'] == 'x86_64-unknown-linux-gnu']
    assert layout['size'] == size and layout['align'] == 8
    assert layout['repr']['transparent'] is True
    assert layout['variant_layouts'][0]['field_offsets'] == [0]

cast_rows = {
    ('Transmute', 5284, 5283): 'sharedFatToNonNullFat',
    ('Transmute', 5283, 5286): 'nonNullFatToMutFat',
    ('RawPtr', 5286, 4603): 'mutFatToMutThin',
    ('Transmute', 4603, 4176): 'mutThinToNonNullThin',
    ('Transmute', 4176, 4603): 'nonNullThinToMutThin',
    ('RawPtr', 4603, 4178): 'mutThinToSharedThin',
    ('Transmute', 887, 4178): 'wordToSharedThin',
}
rows = []
def ident(ref):
    if 'Deduplicated' in ref: return ref['Deduplicated']
    return ref['HashConsedValue'][0]
def local(place):
    assert list(place['kind']) == ['Local']
    return place['kind']['Local']
def copied(operand):
    assert list(operand) == ['Copy']
    return local(operand['Copy'])
def metadata(operand):
    assert list(operand) == ['Copy']
    place = operand['Copy']
    base, projection = place['kind']['Projection']
    assert projection == 'PtrMetadata' and ident(place['ty']) == 887
    return local(base)
def block(value, path):
    statements = [statement(s, path + ['statements', i]) for i, s in enumerate(value['statements'])]
    return '.seq ' + ' '.join('(' + s + ')' for s in statements) if len(statements) == 2 else sequence(statements)
def sequence(statements):
    if not statements: return '.nop'
    return '.seq (' + statements[0] + ') (' + sequence(statements[1:]) + ')'
def statement(value, path):
    kind = value['kind']
    row = {'path': path, 'statement_id': value['id'], 'source_kind': kind}
    rows.append(row)
    if isinstance(kind, str):
        assert kind == 'Return'
        result = '.one .ret'
    elif 'StorageLive' in kind: result = f'.one (.live {kind["StorageLive"]})'
    elif 'StorageDead' in kind: result = f'.one (.dead {kind["StorageDead"]})'
    elif 'Assign' in kind:
        dest, expr = kind['Assign']
        dst = local(dest)
        if 'Use' in expr:
            operand, moved = expr['Use']
            assert moved == 'No' and ident(dest['ty']) == 887
            result = f'.one (.metadata {dst} {metadata(operand)})'
        elif 'RawPtr' in expr:
            x = expr['RawPtr']
            base, projection = x['place']['kind']['Projection']
            assert projection == 'Deref' and x['kind'] == 'Shared'
            assert resolve(x['place']['ty']) == slice_qm31
            assert ident(dest['ty']) == 5284
            result = f'.one (.rawSlice {dst} {local(base)} {metadata(x["ptr_metadata"])})'
        elif 'UnaryOp' in expr:
            op, operand = expr['UnaryOp']
            assert list(op) == ['Cast'] and len(op['Cast']) == 1
            tag, pair = next(iter(op['Cast'].items()))
            src_ty, dst_ty = map(ident, pair)
            assert ident(operand['Copy']['ty']) == src_ty and ident(dest['ty']) == dst_ty
            name = cast_rows[(tag, src_ty, dst_ty)]
            result = f'.one (.cast {dst} {copied(operand)} .{name})'
            row['resolved_cast_types'] = [resolve(pair[0]), resolve(pair[1])]
        elif 'BinaryOp' in expr:
            op, ptr, count = expr['BinaryOp']
            assert op == 'Offset' and ident(dest['ty']) == 4603
            assert ident(ptr['Copy']['ty']) == 4603 and ident(count['Copy']['ty']) == 887
            result = f'.one (.offset {dst} {copied(ptr)} {copied(count)})'
        elif 'Aggregate' in expr:
            agg, operands = expr['Aggregate']
            adt, variant, active_field = agg['Adt']
            assert variant is None and active_field is None and adt['generics'] == empty
            if adt['id'] == {'Adt': 59}:
                assert operands == [] and ident(dest['ty']) == 4182
                result = f'.one (.marker {dst})'
            else:
                assert adt['id'] == {'Adt': 42} and len(operands) == 3
                assert ident(dest['ty']) == 2765
                first, last, marker = operands
                assert ident(first['Copy']['ty']) == 4176 and ident(last['Copy']['ty']) == 4178
                assert list(marker) == ['Move'] and ident(marker['Move']['ty']) == 4182
                result = f'.one (.iterator {dst} {copied(first)} {copied(last)} {local(marker["Move"])})'
        else: raise ValueError(('unsupported assign', path, expr))
    elif 'Switch' in kind:
        test, yes, no = kind['Switch']['If']
        assert test == {'Copy': {'kind': {'Global': {'id': 31, 'generics': empty}}, 'ty': {'Deduplicated': 971}}}
        result = f'.globalIf 31 ({block(yes, path+["Switch", "If", 1])}) ({block(no, path+["Switch", "If", 2])})'
    else: raise ValueError(('unsupported statement', path, kind))
    row['projection'] = result
    return result

body = tree['fun_decls'][86]['body']['Structured']['body']
assert len(body['statements']) == 28
projected = block(body, ['translated', 'fun_decls', 86, 'body', 'Structured', 'body'])
assert len(rows) == 36
text = '''import AspisV8R19.R473SequenceRegrouping

/-! Generated syntactic projection of R440 constructor86. The generator checks
every supported native operation and operand and retains both branch arms.
This is not a certified JSON decoder or a Rust/LLBC memory-semantics theorem. -/
set_option autoImplicit false
namespace AspisV8R19.R474NativeConstructorProjection
open AspisV8R19.R432PointerPrimitive
open AspisV8R19.R433ConstructorFragment

def selected : Program :=
  ''' + projected + '''

theorem execution_matches {T : Type} (heap : Heap T) (locals : Locals) :
    R472CheckedConstructor.program heap locals selected =
      R472CheckedConstructor.program heap locals constructor86 := by
  calc
    _ = R472CheckedConstructor.program heap locals
        (R473SequenceRegrouping.normalize selected) :=
      (R473SequenceRegrouping.normalize_execution heap selected locals).symm
    _ = R472CheckedConstructor.program heap locals
        (R473SequenceRegrouping.normalize constructor86) := by rfl
    _ = _ := R473SequenceRegrouping.normalize_execution heap constructor86 locals

def execute {T : Type} (heap : Heap T) (ptr : Pointer)
    (length : Nat) : Option Iter := do
  let .returned (.iterator iter) _ ←
    R472CheckedConstructor.program heap (initial ptr length) selected | none
  some iter

theorem complete_checked_fragment {T : Type} (heap : Heap T)
    (ptr : Pointer) (length : Nat) (hptr : 0 < ptr.address) :
    execute heap ptr length = newIter heap ptr length := by
  unfold execute
  rw [execution_matches]
  exact R472CheckedConstructor.complete_constructor heap ptr length hptr

#print axioms selected
#print axioms execution_matches
#print axioms execute
#print axioms complete_checked_fragment
end AspisV8R19.R474NativeConstructorProjection
'''
if args.check:
    assert args.target.read_text() == text, 'generated file differs'
else:
    args.target.write_text(text)
receipt = {'boundary': __doc__, 'input_sha256': source_hash,
    'target_sha256': hashlib.sha256(text.encode()).hexdigest(),
    'statement_count': len(rows), 'rows': rows,
    'source_semantics_proved': False}
if not args.check:
    args.target.with_suffix('.projection.json').write_text(json.dumps(receipt, indent=2)+'\n')
print(json.dumps({k: receipt[k] for k in ['input_sha256', 'target_sha256', 'statement_count', 'source_semantics_proved']}))
