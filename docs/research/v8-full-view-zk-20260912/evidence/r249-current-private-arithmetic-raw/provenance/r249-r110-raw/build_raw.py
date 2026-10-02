#!/usr/bin/env python3
"""Rebuild the R249 raw adapter and its mechanical binding audit."""
from pathlib import Path
import hashlib, json, re

ROOT = Path(__file__).resolve().parents[2]
GEN = ROOT / '.r21-scratch/r247-r110-leaf-translation/generated/AspisR247R110Leaves'
PIN = ROOT / 'docs/research/v8-full-view-zk-20260912/lean/AspisR156FullFreeze/FunsCore.lean'
OUT = Path(__file__).resolve().parent
funs_path, types_path = GEN/'Funs.lean', GEN/'Types.lean'
funs, types, pinned = funs_path.read_text(), types_path.read_text(), PIN.read_text()
selected_functions = [
 'circle_norm.joined_inverse.line_norm.r110_norm.B.input',
 'circle_norm.joined_inverse.line_norm.r110_norm.B.reduce',
 'circle_norm.joined_inverse.line_norm.r110_norm.B.add',
 'circle_norm.joined_inverse.line_norm.r110_norm.B.sub',
 'circle_norm.joined_inverse.line_norm.r110_norm.B.half',
 'circle_norm.joined_inverse.line_norm.r110_norm.B.mul',
 'circle_norm.joined_inverse.line_norm.r110_norm.C.output',
 'circle_norm.joined_inverse.line_norm.r110_norm.C.add',
 'circle_norm.joined_inverse.line_norm.r110_norm.C.sub',
 'circle_norm.joined_inverse.line_norm.r110_norm.C.half',
 'circle_norm.joined_inverse.line_norm.r110_norm.C.mul_m',
 'circle_norm.joined_inverse.line_norm.r110_norm.C.mul',
 'circle_norm.joined_inverse.line_norm.r110_norm.C.square',
 'circle_norm.joined_inverse.line_norm.r110_norm.C.times_r',
 'circle_norm.joined_inverse.line_norm.r110_norm.C.norm',
 'circle_norm.joined_inverse.line_norm.r110_norm.C.double',
]
globals_ordered = [
 'circle_norm.joined_inverse.line_norm.r110_norm.P110',
 'circle_norm.joined_inverse.line_norm.r110_norm.C.mul.PP',
]
selected = [globals_ordered[0]] + selected_functions[:6] + selected_functions[6:11] + [globals_ordered[1]] + selected_functions[11:]

def blocks(text):
    starts = [m.start() for m in re.finditer(r'(?m)^/--', text)]
    out = {}
    for i,start in enumerate(starts):
        end = starts[i+1] if i+1 < len(starts) else len(text)
        block = text[start:end].strip()
        block = re.sub(r'\nend AspisR247R110Leaves\s*$', '', block).strip()
        m = re.search(r'(?m)^def ([\w.]+)', block)
        if m:
            out[m.group(1)] = block
    return out

def norm(s): return re.sub(r'\s+', ' ', s).strip()
def body_only(s): return s[s.index('def '):]

def sha(s): return hashlib.sha256(s.encode()).hexdigest()

fb, tb, pb = blocks(funs), blocks(types), blocks(pinned)
assert all(n in fb for n in selected), [n for n in selected if n not in fb]
assert len(selected_functions) == 16 and len(globals_ordered) == 2
assert 'end AspisR247R110Leaves' not in fb[selected[-1]]
type_names = ['circle_norm.joined_inverse.line_norm.r110_norm.B',
              'circle_norm.joined_inverse.line_norm.r110_norm.C']
assert all(n in tb for n in type_names)
assert norm(body_only(tb[type_names[0]])).endswith(':= Std.U32')
assert norm(body_only(tb[type_names[1]])).endswith(':= circle_norm.joined_inverse.line_norm.r110_norm.B × circle_norm.joined_inverse.line_norm.r110_norm.B')
# The generated wrappers call these field declarations; the adapter intentionally
# resolves them through the imported pinned R156 namespace.
external = ['aspis_core.field.P','aspis_core.field.reduce_u64',
            'aspis_core.field.M31.reduce_u64','aspis_core.field.CM31.new']
assert all(n in fb and n in pb for n in external), [(n,n in fb,n in pb) for n in external]
repls = [
 ('core.num.U32.wrapping_add','Std.U32.wrapping_add'),
 ('core.num.U32.wrapping_sub','Std.U32.wrapping_sub'),
 ('core.num.U64.wrapping_add','Std.U64.wrapping_add'),
 ('core.num.U64.wrapping_sub','Std.U64.wrapping_sub'),
 ('Std.U32.wrapping_shr self 1#i32','Std.U32.wrapping_shr self 1#u32'),
 ('Std.U32.wrapping_shl i1 30#i32','Std.U32.wrapping_shl i1 30#u32'),
 ('Std.U64.wrapping_shr x 31#i32','Std.U64.wrapping_shr x 31#u32'),
]
count = {a:sum(fb[n].count(a) for n in selected_functions) for a,_ in repls}
expected = [2,1,2,1,1,1,1]
assert list(count.values()) == expected, count
adapted = {}
for n in selected:
    body=fb[n]
    for a,b in repls: body=body.replace(a,b)
    adapted[n]=body

header = '''import Aeneas.Std
import AspisR156FullFreeze.FunsCore
open Aeneas Aeneas.Std Result ControlFlow Error
open AspisR156FullFreeze
set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false

noncomputable section
namespace AspisR249R110Raw

/-- Generated r110_norm private scalar representation, fixed to the pinned word API. -/
@[reducible] def circle_norm.joined_inverse.line_norm.r110_norm.B := Std.U32
/-- Generated r110_norm private pair representation. -/
def circle_norm.joined_inverse.line_norm.r110_norm.C :=
  circle_norm.joined_inverse.line_norm.r110_norm.B ×
  circle_norm.joined_inverse.line_norm.r110_norm.B

'''
body='\n\n'.join(adapted[n] for n in selected)
counts = '''
/-- Aeneas' generated nonnegative signed count 1 and the pinned unsigned count agree. -/
theorem count_one : (1#i32 : I32).bv.toNat = (1#u32 : U32).val := by decide
/-- Aeneas' generated nonnegative signed count 30 and the pinned unsigned count agree. -/
theorem count_thirty : (30#i32 : I32).bv.toNat = (30#u32 : U32).val := by decide
/-- Aeneas' generated nonnegative signed count 31 and the pinned unsigned count agree. -/
theorem count_thirty_one : (31#i32 : I32).bv.toNat = (31#u32 : U32).val := by decide

'''
prints='\n'.join(f'#print axioms {n}' for n in selected)
prints = '#print axioms circle_norm.joined_inverse.line_norm.r110_norm.B\n#print axioms circle_norm.joined_inverse.line_norm.r110_norm.C\n' + prints
prints += '\n#print axioms count_one\n#print axioms count_thirty\n#print axioms count_thirty_one'
lean=header+body+'\n'+counts+prints+'\nend AspisR249R110Raw\nend'
lean_path=OUT/'AspisR249R110Raw.lean'
lean_path.write_text(lean)

ext_checks=[]
for n in external:
    ext_checks.append({'name':n,'generated_normalized_sha256':sha(norm(body_only(fb[n]))),
      'pinned_R156_normalized_sha256':sha(norm(body_only(pb[n]))),
      'normalized_body_equal':norm(body_only(fb[n]))==norm(body_only(pb[n])),
      'binding':'open AspisR156FullFreeze; no local shadow declaration'})
assert all(x['normalized_body_equal'] for x in ext_checks), ext_checks
alias_checks=[]
for n in type_names:
    alias_checks.append({'name':n,'generated_type_sha256':sha(norm(body_only(tb[n]))),
      'adapter_alias':'Std.U32' if n.endswith('.B') else 'B × B',
      'generated_reducible_attribute_preserved':('[reducible]' in tb[n]) == n.endswith('.B')})
source_to_output=[]
for n in selected:
    before,after=fb[n],adapted[n]
    source_to_output.append({'name':n,'source_normalized_sha256':sha(norm(before)),
      'adapter_normalized_sha256':sha(norm(after)),
      'exact_authorized_replacements_applied':[{ 'from':a,'to':b,'count':before.count(a)} for a,b in repls if before.count(a)],
      'source_body_preserved_after_declared_replacements':norm(after)==norm(__import__('functools').reduce(lambda s,p:s.replace(*p),repls,before))})

# Traverse generated dependency names to capture its visible project call closure.
all_names=set(fb)
reachable=set(); queue=selected[:]
while queue:
    n=queue.pop(0)
    text=fb[n]
    for dep in all_names:
        if dep != n and re.search(r'(?<![\w.])'+re.escape(dep)+r'(?![\w.])',text) and dep not in reachable:
            reachable.add(dep); queue.append(dep)

r239_audit=ROOT/'.r21-scratch/r239-coefficient-raw/transitive-binding-audit.json'
prior=json.loads(r239_audit.read_text())
reducer_evidence={
 'reuse_source':str(r239_audit.relative_to(ROOT)),
 'prior_audit_scope':prior.get('coverage'),
 'prior_reachable_R238_declaration_count':prior.get('reachable_R238_declaration_count'),
 'prior_reducer_chain_declarations':[x for x in prior.get('reachable_R238_declarations',[]) if any(k in x for k in ('reduce_u64','r23_product','r91_raw','field.P','M31.mul'))],
 'limitation':'Reuse only as pinned R156/R221 declaration-text and existing API adaptation evidence; this R249 audit adds no execution or source-semantics conclusion.'}

src_hashes={str(p.relative_to(ROOT)):sha(p.read_text()) for p in [funs_path,types_path,PIN,r239_audit]}
audit={'artifact':'R249 raw adapter binding audit','scope':'Mechanical declaration-text extraction and pinned-name binding; no Lean/build execution.',
 'selected_generated_r110_functions':selected_functions,'selected_function_count':len(selected_functions),
 'selected_generated_r110_globals':globals_ordered,'selected_definition_count':len(selected),
 'explicitly_excluded':['circle_norm.joined_inverse.line_norm.r110_norm.C.input'],
 'aliases':{'B':'Std.U32','C':'B × B'},'alias_body_checks':alias_checks,'replacement_counts':dict(zip([a+' -> '+b for a,b in repls],expected)),
 'external_R156_bindings':ext_checks,'selected_body_checks':source_to_output,
 'reachable_generated_declarations':sorted(reachable), 'reducer_dependency_evidence':reducer_evidence,
 'input_sha256':src_hashes,'output_sha256':{'AspisR249R110Raw.lean':sha(lean)}}
(OUT/'binding-audit.json').write_text(json.dumps(audit,indent=2)+'\n')
md=['# R249 R110 raw adapter binding audit','',audit['scope'],'',
    f"The adapter preserves {len(selected_functions)} generated leaf bodies and both generated globals, for {len(selected)} retained definitions, and defines the requested aliases `B := Std.U32`, `C := B × B`.",'',
    'The only source-body substitutions are:', '']
for (a,b),c in zip(repls,expected): md.append(f'- `{a}` → `{b}` ({c} occurrence(s)).')
md += ['', 'The generated `aspis_core.field.P`, `reduce_u64`, `M31.reduce_u64`, and `CM31.new` blocks were checked against pinned R156 declarations after whitespace normalization; all four match. The adapter declares no local copies, and `open AspisR156FullFreeze` binds those names to R156.', '',
       'The transitive reducer chain reuses the existing R239 R156/R221 declaration audit for `M31.mul`, reducer, bounded product, raw add/sub, and P dependencies. This is text/binding evidence only; it makes no source-semantics or runtime claim.', '',
       'The adapter adds `count_one`, `count_thirty`, and `count_thirty_one` ground `decide` lemmas for the generated signed literals and their pinned unsigned API counts. No build or Lean execution was run.', '',
       'SHA-256 checksums are recorded in `binding-audit.SHA256SUMS`.']
(OUT/'binding-audit.md').write_text('\n'.join(md)+'\n')
# Checksums cover inputs, generated source, generator, and audit outputs; avoid self-reference.
files=[funs_path,types_path,PIN,r239_audit,Path(__file__),lean_path,OUT/'binding-audit.json',OUT/'binding-audit.md']
(OUT/'binding-audit.SHA256SUMS').write_text(''.join(f'{hashlib.sha256(p.read_bytes()).hexdigest()}  {p.relative_to(ROOT)}\n' for p in files))
print(json.dumps({'defs':len(selected),'replacements':dict(zip([a+' -> '+b for a,b in repls],expected)),'external_R156_equal':all(x['normalized_body_equal'] for x in ext_checks),'output':str(lean_path)},indent=2))
