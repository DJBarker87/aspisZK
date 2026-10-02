#!/usr/bin/env python3
"""Rebuild the R264 selected raw coefficient adapter and binding audit."""
from pathlib import Path
import hashlib
import json
import re

ROOT = Path(__file__).resolve().parents[2]
GEN = ROOT / '.r21-scratch/r263-private-coefficient-translation/generated/AspisR263PrivateCoefficient'
R249 = ROOT / '.r21-scratch/r249-r110-raw/AspisR249R110Raw.lean'
R259 = ROOT / '.r21-scratch/r259-private-input-raw/AspisR259PrivateInputRaw.lean'
R156_FUNS = ROOT / 'docs/research/v8-full-view-zk-20260912/lean/AspisR156FullFreeze/FunsCore.lean'
R156_TYPES = ROOT / 'docs/research/v8-full-view-zk-20260912/lean/AspisR156FullFreeze/Types.lean'
OUT = Path(__file__).resolve().parent
funs_path, types_path = GEN/'Funs.lean', GEN/'Types.lean'
funs, types = funs_path.read_text(), types_path.read_text()
r249_text, r259_text = R249.read_text(), R259.read_text()
r156_funs, r156_types = R156_FUNS.read_text(), R156_TYPES.read_text()

private = 'circle_norm.joined_inverse.line_norm.r110_norm.'
selected_types = [private+'Coeff110.new.closure', private+'Coeff110.new.closure_1', private+'Coeff110']
selected_funs = [
 private+'Coeff110.new.closure.Insts.CoreOpsFunctionFnTupleArrayC2C.call',
 private+'Coeff110.new.closure_1.Insts.CoreOpsFunctionFnPairArrayC2ArrayC2C.call',
 private+'Coeff110.new',
 private+'Coeff110.four',
]

# Only the historical R249 type/API adaptations are applied to helper comparisons.
adaptations = [
 ('core.num.U32.wrapping_add','Std.U32.wrapping_add'),
 ('core.num.U32.wrapping_sub','Std.U32.wrapping_sub'),
 ('core.num.U64.wrapping_add','Std.U64.wrapping_add'),
 ('core.num.U64.wrapping_sub','Std.U64.wrapping_sub'),
 ('Std.U32.wrapping_shr self 1#i32','Std.U32.wrapping_shr self 1#u32'),
 ('Std.U32.wrapping_shl i1 30#i32','Std.U32.wrapping_shl i1 30#u32'),
 ('Std.U64.wrapping_shr x 31#i32','Std.U64.wrapping_shr x 31#u32'),
]

def decls(text):
    starts = [m.start() for m in re.finditer(r'(?m)^/--', text)]
    out = {}
    for i, start in enumerate(starts):
        end = starts[i+1] if i+1 < len(starts) else len(text)
        block = text[start:end].strip()
        block = re.split(r'(?m)^#print axioms ', block, maxsplit=1)[0].strip()
        block = re.sub(r'\nend AspisR\d+\w*\s*$', '', block).strip()
        m = re.search(r'(?m)^.*?\b(?:def|structure)\s*\n?\s*([\w.]+)', block)
        if m:
            out[m.group(1)] = block
    return out

def norm(s):
    return re.sub(r'\s+', ' ', s).strip()

def body(s):
    # Declarations may carry attributes on the same line as `def` (for
    # example R249's `@[reducible] def ...B := Std.U32`). Start at the
    # declaration keyword so body comparisons ignore docs/attributes.
    m = re.search(r'(?m)^.*?\b(def|structure)\s+', s)
    if m is None:
        raise ValueError('declaration body start not found')
    return s[m.start(1):]

def sha(s):
    return hashlib.sha256(s.encode()).hexdigest()

fb, tb = decls(funs), decls(types)
r249d, r259d, r156f, r156t = map(decls, [r249_text, r259_text, r156_funs, r156_types])
assert all(n in tb for n in selected_types)
assert all(n in fb for n in selected_funs)

# Keep the source declaration blocks whole: documentation and attributes travel with each block.
selected_blocks = [tb[n] for n in selected_types] + [fb[n] for n in selected_funs]
header = '''import AspisR259PrivateInputRaw
open Aeneas Aeneas.Std Result ControlFlow Error
open AspisR259PrivateInputRaw
open AspisR249R110Raw
open AspisR156FullFreeze
set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false

namespace AspisR264PrivateCoefficientRaw

'''
axiom_audit = '''
#print axioms circle_norm.joined_inverse.line_norm.r110_norm.Coeff110.new.closure
#print axioms circle_norm.joined_inverse.line_norm.r110_norm.Coeff110.new.closure_1
#print axioms circle_norm.joined_inverse.line_norm.r110_norm.Coeff110
#print axioms circle_norm.joined_inverse.line_norm.r110_norm.Coeff110.new.closure.Insts.CoreOpsFunctionFnTupleArrayC2C.call
#print axioms circle_norm.joined_inverse.line_norm.r110_norm.Coeff110.new.closure_1.Insts.CoreOpsFunctionFnPairArrayC2ArrayC2C.call
#print axioms circle_norm.joined_inverse.line_norm.r110_norm.Coeff110.new
#print axioms circle_norm.joined_inverse.line_norm.r110_norm.Coeff110.four
'''
lean = header + '\n\n'.join(selected_blocks) + '\n\n' + axiom_audit + 'end AspisR264PrivateCoefficientRaw\n'
lean_path = OUT/'AspisR264PrivateCoefficientRaw.lean'
lean_path.write_text(lean)

selected_checks=[]
for n, block in zip(selected_types+selected_funs, selected_blocks):
    src = tb[n] if n in selected_types else fb[n]
    selected_checks.append({'name':n,'source_block_sha256':sha(src),
      'adapter_block_sha256':sha(block),'exact_block_copy':src==block,
      'adaptation_count':0})
assert all(x['exact_block_copy'] for x in selected_checks)

# Follow generated project declaration calls transitively from the four copied bodies.
all_fun_names=set(fb)
reachable=set()
queue=selected_funs[:]
while queue:
    name=queue.pop(0)
    source_block=fb[name]
    for dep in all_fun_names:
        if dep != name and dep not in reachable and re.search(r'(?<![\w.])'+re.escape(dep)+r'(?![\w.])',source_block):
            reachable.add(dep)
            queue.append(dep)

helper_checks=[]
unresolved=[]
for name in sorted(reachable):
    if name in selected_funs or name in selected_types:
        continue
    if name.startswith(private):
        source=fb.get(name)
        if source is None:
            unresolved.append({'name':name,'reason':'referenced generated private declaration absent from Funs.lean'})
            continue
        if name in r249d:
            target=r249d[name]
            adapted=body(source)
            applied=[]
            for old,new in adaptations:
                count=adapted.count(old)
                if count:
                    applied.append({'from':old,'to':new,'count':count})
                    adapted=adapted.replace(old,new)
            equal=norm(adapted)==norm(body(target))
            helper_checks.append({'name':name,'target':'R249','source_body_sha256':sha(norm(body(source))),
              'target_body_sha256':sha(norm(body(target))), 'adapted_source_body_sha256':sha(norm(adapted)),
              'documented_adaptations':applied,'normalized_equal_after_documented_adaptations':equal})
            if not equal:
                unresolved.append({'name':name,'target':'R249','reason':'body mismatch remains after only documented adaptations',
                  'source_normalized':norm(adapted),'target_normalized':norm(body(target))})
        elif name in r259d:
            target=r259d[name]
            equal=norm(body(source))==norm(body(target))
            helper_checks.append({'name':name,'target':'R259','source_body_sha256':sha(norm(body(source))),
              'target_body_sha256':sha(norm(body(target))), 'documented_adaptations':[],
              'normalized_equal_after_documented_adaptations':equal})
            if not equal:
                unresolved.append({'name':name,'target':'R259','reason':'body mismatch; no adaptation authorized',
                  'source_normalized':norm(body(source)),'target_normalized':norm(body(target))})
        else:
            unresolved.append({'name':name,'reason':'private helper has no body in R249 or R259'})
    elif name.startswith('core.option.'):
        source=fb.get(name)
        target=r259d.get(name)
        if source is None or target is None:
            unresolved.append({'name':name,'target':'R259','reason':'Option helper declaration missing on one side'})
            continue
        equal=norm(body(source))==norm(body(target))
        helper_checks.append({'name':name,'target':'R259','source_body_sha256':sha(norm(body(source))),
          'target_body_sha256':sha(norm(body(target))), 'documented_adaptations':[],
          'normalized_equal_after_documented_adaptations':equal})
        if not equal:
            unresolved.append({'name':name,'target':'R259','reason':'body mismatch; no adaptation authorized',
              'source_normalized':norm(body(source)),'target_normalized':norm(body(target))})
    elif name.startswith('aspis_core.field.'):
        source=fb.get(name)
        target=r156f.get(name)
        if source is None or target is None:
            unresolved.append({'name':name,'target':'R156','reason':'external field declaration unavailable for body comparison'})
            continue
        equal=norm(body(source))==norm(body(target))
        helper_checks.append({'name':name,'target':'R156','source_body_sha256':sha(norm(body(source))),
          'target_body_sha256':sha(norm(body(target))), 'documented_adaptations':[],
          'normalized_equal_after_documented_adaptations':equal})
        if not equal:
            unresolved.append({'name':name,'target':'R156','reason':'external body mismatch; no adaptation authorized'})

# QM31 is an external type, not copied or shadowed. Compare the generated representation to pinned R156.
qm31='aspis_core.field.QM31'
assert qm31 in tb and qm31 in r156t
qm31_equal=norm(body(tb[qm31]))==norm(body(r156t[qm31]))
qm31_check={'name':qm31,'generated_representation_sha256':sha(norm(body(tb[qm31]))),
  'pinned_R156_representation_sha256':sha(norm(body(r156t[qm31]))),
  'normalized_equal':qm31_equal,'local_shadow_declared':False}
if not qm31_equal:
    unresolved.append({'name':qm31,'target':'R156.Types','reason':'QM31 representation mismatch; generated type is not copied'})

# Type aliases B and C resolve through R249. Include their declaration comparisons as helper evidence.
for name in [private+'B', private+'C']:
    source=tb.get(name); target=r249d.get(name)
    if source is None or target is None:
        unresolved.append({'name':name,'target':'R249','reason':'private representation alias unavailable'})
        continue
    equal=norm(body(source))==norm(body(target))
    helper_checks.append({'name':name,'target':'R249.Types','source_body_sha256':sha(norm(body(source))),
      'target_body_sha256':sha(norm(body(target))),'documented_adaptations':[],
      'normalized_equal_after_documented_adaptations':equal})
    if not equal:
        unresolved.append({'name':name,'target':'R249.Types','reason':'alias mismatch; no adaptation authorized'})

input_paths=[funs_path,types_path,R249,R259,R156_FUNS,R156_TYPES]
input_hashes={str(p.relative_to(ROOT)):hashlib.sha256(p.read_bytes()).hexdigest() for p in input_paths}
audit={'artifact':'R264 private coefficient raw adapter audit',
 'scope':'Declaration-text/binding comparison only; no compilation or source-semantics conclusion.',
 'selected_aliases':selected_types,'selected_functions':selected_funs,
 'selected_count':len(selected_blocks),'selected_body_checks':selected_checks,
 'reachable_generated_helper_names':sorted(reachable),'helper_body_checks':helper_checks,
 'QM31_R156_representation_check':qm31_check,'unresolved_mismatches':unresolved,
 'adaptations_allowed':adaptations,'adaptations_in_selected_bodies':0,
 'all_selected_exact_copies':all(x['exact_block_copy'] for x in selected_checks),
 'all_referenced_helper_bodies_match':not unresolved,
 'input_sha256':input_hashes,'output_sha256':{'AspisR264PrivateCoefficientRaw.lean':sha(lean)}}
(OUT/'binding-audit.json').write_text(json.dumps(audit,indent=2)+'\n')

md=['# R264 private coefficient raw binding audit','',audit['scope'],'',
 'The raw adapter copies the three requested aliases and four function bodies exactly, preserving their docstrings and attributes. The selected bodies required zero replacements.', '',
 'The generated `QM31` structure was compared with the pinned R156 `QM31` declaration and is not locally redeclared.', '',
 'Every reachable generated helper body is compared against the R249 private adapter, the R259 Option/C-input adapter, or the pinned R156 field declaration. R249 comparisons allow only the recorded wrapper qualification and unsigned literal count adaptations:', '']
for old,new in adaptations:
    md.append(f'- `{old}` → `{new}`')
md += ['', f"Reachable generated helper declarations checked: {len(helper_checks)}.", '']
if unresolved:
    md += ['## Unresolved mismatches','']
    for row in unresolved:
        md.append(f"- `{row['name']}` ({row.get('target','unknown target')}): {row['reason']}")
else:
    md.append('No unresolved declaration-body mismatches were found within the audited dependency closure.')
md += ['', 'The audit records input/output SHA-256 values in `binding-audit.json`; the reproducible generator and checksum file are in this directory. No build or Lean execution was run.', '']
(OUT/'binding-audit.md').write_text('\n'.join(md))
files=[*input_paths,Path(__file__),lean_path,OUT/'binding-audit.json',OUT/'binding-audit.md']
(OUT/'binding-audit.SHA256SUMS').write_text(''.join(
 f'{hashlib.sha256(p.read_bytes()).hexdigest()}  {p.relative_to(ROOT)}\n' for p in files))
print(json.dumps({'selected':len(selected_blocks),'reachable_helpers':len(reachable),
 'helper_checks':len(helper_checks),'unresolved':len(unresolved),'qm31_equal':qm31_equal,
 'exact_selected_copies':all(x['exact_block_copy'] for x in selected_checks)},indent=2))
