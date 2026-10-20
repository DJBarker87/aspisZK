#!/usr/bin/env python3
"""AST census of a frozen-source superset; NOT a typed call graph or proof.
Requires tree-sitter==0.25.2 and tree-sitter-rust==0.24.2.
Reads git blobs, never rewrites shipped source. --check compares generated data.
"""
import argparse, collections, hashlib, json, re, subprocess
from pathlib import Path
from tree_sitter import Language, Parser
import tree_sitter_rust
ROOT=Path(__file__).resolve().parents[2]
OUT=ROOT/'docs/research/100bit-spend-path-20261013/evidence/r22-overflow-20261021'
FREEZE='b2727acd3abf79315d18b754a260f58f4b1c6326'
def git(*args): return subprocess.check_output(['git','-C',str(ROOT),*args])
def sha(x): return hashlib.sha256(x).hexdigest()
def blob(p): return git('show',FREEZE+':'+p)
def walk(n):
    yield n
    for c in n.named_children: yield from walk(c)
def text(n,b): return b[n.start_byte:n.end_byte].decode()
def owner(n,b):
    parts=[]
    while n:
        if n.type in ('function_item','const_item','static_item','mod_item'):
            x=n.child_by_field_name('name')
            if x: parts.append(text(x,b))
        elif n.type=='impl_item':
            x=n.child_by_field_name('type')
            if x: parts.append(text(x,b))
        n=n.parent
    return '::'.join(reversed(parts)) or '<module>'
def make():
    allpaths=git('ls-tree','-r','--name-only',FREEZE).decode().splitlines()
    paths=[p for p in allpaths if p.endswith('.rs') and (p.startswith(('crates/aspis-r1-cost-probe/src/','programs/r1-cost-probe/src/','programs/aspis-pool/src/')))]
    paths += ['crates/aspis-core/src/'+p for p in ['field.rs','field/wide_exact.rs','circle.rs','digest.rs','r0/domain.rs','r0/merkle.rs','r0/mod.rs','state_only_private_merkle.rs','r0_transcript.rs','r0/transcript.rs','transcript.rs','r0/heap.rs','r0/transport.rs','state_only_prefix.rs']]
    # Pin statement/Pool dependencies too: lexical superset deliberately includes
    # retired/prover/test code, so absence of a typed reachability proof is visible.
    paths += [p for p in allpaths if p.endswith('.rs') and p.startswith('crates/aspis-statement/src/pool_v1/')]
    declpath=ROOT/'docs/research/100bit-spend-path-20261013/tools/tx1-caller-extraction-kit/input-accumulator/source-pins.json'
    declarations=json.loads(declpath.read_text())
    paths += [r['path'] for r in declarations['cuts']+declarations['base52_cuts']]
    parser=Parser(Language(tree_sitter_rust.language()))
    rows=[]; sources=[]
    for p in sorted(set(paths)):
        b=blob(p); tree=parser.parse(b)
        assert not tree.root_node.has_error,p
        sources.append(dict(path=p,sha256=sha(b),bytes=len(b),current_equal=(ROOT/p).read_bytes()==b))
        for n in walk(tree.root_node):
            kind=None; op=None
            if n.type in ('binary_expression','compound_assignment_expr'):
                opnode=n.child_by_field_name('operator')
                op=text(opnode,b) if opnode else None
                if op in ['+','-','*','/','%','<<','>>','+=','-=','*=','/=','%=','<<=','>>=']: kind='operator'
            elif n.type=='unary_expression' and n.children and text(n.children[0],b)=='-': kind='unary_operator';op='-'
            elif n.type=='for_expression': kind='iteration_boundary'
            elif n.type=='index_expression': kind='index'
            elif n.type=='type_cast_expression': kind='cast'
            elif n.type=='call_expression':
                f=n.child_by_field_name('function'); ft=text(f,b) if f else ''
                if any(y+x in ft for x in ['wrapping_','checked_','overflowing_','saturating_','rotate_','reverse_bits'] for y in ['.','::']): kind='integer_method';op=ft
                elif re.search(r'(?:\.|::)(?:add|sub|mul|div|rem|neg|shl|shr|pow|abs|unsigned_abs|next_power_of_two|div_ceil|sum|product)(?:\s*::\s*<.*>)?$',ft): kind='arithmetic_call';op=ft
            if kind:
                expression=(b[n.start_byte:n.child_by_field_name('body').start_byte].decode() if kind=='iteration_boundary' else text(n,b))
                rows.append(dict(id=f'{p}:{n.start_point.row+1}:{n.start_point.column+1}:{kind}',path=p,line=n.start_point.row+1,column=n.start_point.column+1,owner=owner(n,b),kind=kind,operator=op,expression=expression,expression_sha256=sha(expression.encode()),result='UNCLASSIFIED: lexical superset; caller/type/reachability review required'))
    return dict(schema='r22-frozen-ast-census-v1',source_revision=FREEZE,declaration_inventory=dict(path=str(declpath.relative_to(ROOT)),sha256=sha(declpath.read_bytes()),revision=declarations['revision'],use='source-path union only; does not claim all predecessor bodies match the freeze'),artifact_pins={'verifier':'dfc2a91ab24e1ec4f57debd8f124cb4f6a3c38ba2662b7318e2e4f3b4acdde34','pool':'121f3e29741f510e6dc42d0345fc3c36217600f0be337094855c4a9da2581548'},scope='Conservative lexical superset; includes test/prover/legacy and overloaded field operators. SDK/hash/allocator/other transitive crates not exhaustively expanded. Not an exhaustive typed deployed cone.',sources=sources,counts=dict(collections.Counter(r['kind'] for r in rows)),operations=rows)
if __name__=='__main__':
    a=argparse.ArgumentParser();a.add_argument('--check',action='store_true');args=a.parse_args()
    data=(json.dumps(make(),indent=2,sort_keys=True)+'\n').encode(); target=OUT/'operation-census.json'
    if args.check: assert target.read_bytes()==data,'census drift'
    else: target.write_bytes(data)
    print(json.dumps({'path':str(target.relative_to(ROOT)),'sha256':sha(data),'bytes':len(data)}))
