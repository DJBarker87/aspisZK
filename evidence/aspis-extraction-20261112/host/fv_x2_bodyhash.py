#!/usr/bin/env python3
"""X2: per-function body hashes in the Pool ledger's convention (NIK_census.py on branch research,
evidence/pool-borrow-20261107/NIK_census.py, line 58): parse each .rs file with tree-sitter 0.25.2 /
tree-sitter-rust 0.24.2; for every `function_item` with a body, key = <path>::<enclosing mod / fn names and impl type
texts, outermost first>::<name>, body_sha256 = sha256 of the bytes of the body block (from `{` to `}` inclusive).
The same convention is applied to the two library crates. Reads Git only (`git show <rev>:<file>`).
usage: fv_x2_bodyhash.py <rev> <out.json> <dir>...   (run from the repository root)"""
import hashlib, json, subprocess, sys
sys.dont_write_bytecode = True
sys.path.insert(0, __import__('os').environ.get('X2_TS_PATH', '/private/tmp/NFZ-parser-20261104'))   # tree-sitter 0.25.2 + tree-sitter-rust 0.24.2
from tree_sitter import Language, Parser
import tree_sitter_rust
parser = Parser(Language(tree_sitter_rust.language()))
rev, out, dirs = sys.argv[1], sys.argv[2], sys.argv[3:]
def walk(n):
    yield n
    for c in n.named_children: yield from walk(c)
def ancestors(n):
    while n.parent: n = n.parent; yield n
def text(n, b): return b[n.start_byte:n.end_byte].decode() if n else ''
res = []
for d in dirs:
    for p in subprocess.check_output(['git', 'ls-tree', '-r', '--name-only', rev, d], text=True).splitlines():
        if not p.endswith('.rs'): continue
        b = subprocess.check_output(['git', 'show', rev + ':' + p]); root = parser.parse(b).root_node
        for n in walk(root):
            if n.type != 'function_item' or n.child_by_field_name('body') is None: continue
            body = n.child_by_field_name('body'); scopes = []
            for a in reversed(list(ancestors(n))):
                if a.type in ('mod_item', 'function_item'): scopes.append(text(a.child_by_field_name('name'), b))
                if a.type == 'impl_item': scopes.append(text(a.child_by_field_name('type'), b))
            name = text(n.child_by_field_name('name'), b)
            res.append(dict(key=p + '::' + '::'.join(scopes + [name]), path=p, name=name, start=n.start_point.row + 1, end=n.end_point.row + 1,
                            body_start=body.start_point.row + 1, body_sha256=hashlib.sha256(b[body.start_byte:body.end_byte]).hexdigest(), parse_error=root.has_error))
json.dump(dict(revision=rev, convention='NIK_census.py line 58 (research)', functions=res), open(out, 'w'), indent=1)
print(rev, len(res), 'functions')
