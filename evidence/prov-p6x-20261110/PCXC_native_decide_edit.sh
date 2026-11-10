#!/bin/bash
# PCXC_native_decide_edit.sh: Task 1. Produce the corrected P4e file (Debug fmt definition and its sole wrapper instance removed),
# regenerate bundle PRVCmb_C13 from it with the PCXB rename rule (only C13 changes), and verify the bundle differs from PCXB's C13 by exactly the removal.
set -e
WT=/Users/dominic/ZK/.worktrees/pc-prov-p6x
cd $WT/evidence/prov-p6x-20261110
python3 -I -B - <<'PY'
import json, subprocess, sys, hashlib, difflib
sys.dont_write_bytecode = True
sys.path.insert(0, '../prov-p6c-20261109')
import PCXB_rename as R
WT = '/Users/dominic/ZK/.worktrees/pc-prov-p6x'
SRC = 'evidence/prov-p4e-20261109/PRVEq_AspisR1PrefixAggregateParser_Funs_S3.lean'
def show(p): return subprocess.check_output(['git', '-C', WT, 'show', 'HEAD:' + p]).decode()
orig = show(SRC)
lines = orig.split('\n')
# block: from the doc comment of the fmt definition to the closing brace of the Insts.CoreFmtDebug instance (+ one trailing blank line)
s = next(i for i, l in enumerate(lines) if l.startswith('/-- [aspis_r1_prefix_parser_extract::r1_wire::{impl core::fmt::Debug for'))
inst = next(i for i, l in enumerate(lines) if l.startswith('def r1_wire.Error.Insts.CoreFmtDebug :'))
e = inst
while lines[e] != '}': e += 1
assert lines[e + 1] == ''
removed = '\n'.join(lines[s:e + 2]) + '\n'
new = '\n'.join(lines[:s] + lines[e + 2:])
assert 'CoreFmtDebug' not in new and 'CoreFmtDebug' in orig
open('PCXC_PRVEq_AspisR1PrefixAggregateParser_Funs_S3.lean', 'w').write(new)
open('PCXC_native_decide_removed_text.txt', 'w').write(removed)
sha = lambda t: hashlib.sha256(t.encode()).hexdigest()
# bundle C13
bun = json.load(open('../prov-p6c-20261109/PCXB_BUNDLES.json'))['bundles']
c13 = next(b for b in bun if b['bundle'] == 'PRVCmb_C13')
cf = json.load(open('../prov-p6c-20261109/PCXB_CREDITED_FILES.json'))['files']
def build(subst):
    imports = []; body = []; imports_f = {}
    for j, f in enumerate(c13['files']):
        keep = []; imports_f[f] = []
        for l in (subst.get(f) or show(f)).split('\n'):
            if l.startswith('import '):
                imports_f[f].append(l)
                if l not in imports: imports.append(l)
            else: keep.append(l)
        nc = any(l.strip() == 'noncomputable section' for l in keep)
        tag = c13['tags'][f]
        txt = R.rename('\n'.join(keep), tag, 'import PRVH_WrapAdd' in imports_f[f])
        body += [f'section PRVBundle_{j}', txt] + (['end'] if nc else []) + [f'end PRVBundle_{j}']
    imps = [l for l in imports if l == 'import Aeneas'] + [l for l in imports if l != 'import Aeneas']
    hdr = ['-- PCXB combined-import bundle PRVCmb_C13: exact file texts (import lines hoisted), with declared names renamed by PCXB_rename.py tag C13_Fjj (rule PCXB-C2): ' + ', '.join(x.split('/')[-1] for x in c13['files'])] + imps + ['']
    return '\n'.join(hdr) + '\n'.join(body) + '\n'
old_b = build({})
cur = open('../prov-p6c-20261109/PRVCmb_C13.lean').read()
print('regenerated original C13 equals PCXB C13:', old_b == cur)
assert old_b == cur
new_b = build({SRC: new})
open('PRVCmb_C13.lean', 'w').write(new_b)
d = [l for l in difflib.unified_diff(cur.split('\n'), new_b.split('\n'), lineterm='', n=0) if l[:1] in '+-' and l[:3] not in ('+++', '---')]
print('diff lines: removed', sum(1 for l in d if l[0] == '-'), 'added', sum(1 for l in d if l[0] == '+'))
assert all(l[0] == '-' for l in d), 'bundle diff must be pure removal'
json.dump(dict(file=SRC, original_sha256=sha(orig), new_sha256=sha(new), bundle='PRVCmb_C13', bundle_original_sha256=sha(cur), bundle_new_sha256=sha(new_b),
               removed_lines_in_file=e + 2 - s, removed_lines_in_bundle=len(d)), open('PCXC_native_decide_edit_partial.json', 'w'), indent=1)
print(open('PCXC_native_decide_edit_partial.json').read())
PY
