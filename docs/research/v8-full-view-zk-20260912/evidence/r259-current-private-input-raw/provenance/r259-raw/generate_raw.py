#!/usr/bin/env python3
"""Stage three verbatim R256 declarations over the existing R249 raw namespace."""
from pathlib import Path
import hashlib, json, re

ROOT = Path(__file__).resolve().parents[2]
SRC = ROOT / '.r21-scratch/r256-r110-complete-translation/generated/AspisR256R110CompleteLeaves/Funs.lean'
RAW = ROOT / '.r21-scratch/r249-r110-raw/AspisR249R110Raw.lean'
R245_DECODED = ROOT / '.r21-scratch/r245-r110-leaf-extract/decoded.json'
R255_LLBC = ROOT / '.r21-scratch/r255-r110-complete-ordering/R255R110CompleteOrdered.llbc'
OPTION_ROW = Path(__file__).resolve().parent / 'option-type-source.json'
DISCRIMINANT_BINDING = Path(__file__).resolve().parent / 'discriminant-binding.json'
PINNED_DISCRIMINANT = Path(__file__).resolve().parent / 'pinned-Discriminant.lean'
FAIL_LOG = ROOT / '.r21-scratch/aspis-focus-1790913120788357000.log'
PASS_LOG = ROOT / '.r21-scratch/aspis-focus-1790913218557130000.log'
OUT = Path(__file__).resolve().parent
TARGET = OUT / 'AspisR259PrivateInputRaw.lean'
NAMES = [
    'core.option.Option.Insts.CoreOpsTry_traitTry.branch',
    'core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionInfallible.from_residual',
    'circle_norm.joined_inverse.line_norm.r110_norm.C.input',
]
def sha(b: bytes) -> str:
    return hashlib.sha256(b).hexdigest()
def blocks(src: str):
    starts = [m.start() for m in re.finditer(r'(?m)^/--', src)]
    found = {}
    for i, start in enumerate(starts):
        end = starts[i+1] if i+1 < len(starts) else len(src)
        print_match = re.search(r'(?m)^#print axioms ', src[start:end])
        if print_match: end = start + print_match.start()
        block = src[start:end]
        for name in NAMES:
            if re.search(r'(?m)^def\s+' + re.escape(name) + r'\s*$', block) or re.search(r'(?m)^def\s*$\n\s*' + re.escape(name) + r'\s*$', block):
                if name in found: raise RuntimeError(f'duplicate declaration block: {name}')
                found[name] = block.rstrip() + '\n'
    missing = [n for n in NAMES if n not in found]
    if missing: raise RuntimeError(f'missing generated blocks: {missing}')
    return found
src_bytes = SRC.read_bytes(); src = src_bytes.decode(); raw = RAW.read_bytes()
selected = blocks(src)
header = '''import AspisR249R110Raw

open Aeneas Aeneas.Std Result ControlFlow Error
open AspisR249R110Raw
open AspisR156FullFreeze

set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false

namespace AspisR259PrivateInputRaw

'''
body = '\n'.join(selected[n] for n in NAMES)
support = '''/-- Source-bound Option discriminant support: the R245/R255 Option type row
has None=0 and Some=1, both signed Isize. This fills the pinned builtin
instance gap; it does not alter any of the three generated bodies. -/
def optionTag {T : Type} : Option T → Isize
  | none => 0#isize
  | some _ => 1#isize
local instance optionDiscriminant {T : Type} : Discriminant (Option T) Isize where
  read_discriminant := optionTag

theorem optionTag_none (T : Type) : optionTag (none : Option T) = 0#isize := rfl
theorem optionTag_some {T : Type} (x : T) : optionTag (some x) = 1#isize := rfl

\n'''.replace('\\n','\n')
prints = '''
#print axioms optionTag
#print axioms optionTag_none
#print axioms optionTag_some
#print axioms core.option.Option.Insts.CoreOpsTry_traitTry.branch
#print axioms core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionInfallible.from_residual
#print axioms circle_norm.joined_inverse.line_norm.r110_norm.C.input

end AspisR259PrivateInputRaw
'''
output = header + support + body + prints
TARGET.write_text(output)
emitted = blocks(TARGET.read_text())
checks = []
for n in NAMES:
    a, b = selected[n].encode(), emitted[n].encode()
    checks.append({'name': n, 'source_sha256': sha(a), 'output_sha256': sha(b), 'byte_identical': a == b, 'replacement_count': 0})
assert all(x['byte_identical'] and x['replacement_count'] == 0 for x in checks)
report = {
  'artifact':'R259 private input raw staging',
  'scope':'Mechanical staging only; no compile/build/Lean execution.',
  'imports':['AspisR249R110Raw'],
  'opens':['Aeneas Aeneas.Std Result ControlFlow Error','AspisR249R110Raw','AspisR156FullFreeze'],
  'namespace':'AspisR259PrivateInputRaw',
  'selected_generated_definitions':checks,
  'body_or_attribute_replacements':0,
  'added_source_support': {
    'optionTag': 'Option T → Isize with none ↦ 0#isize, some _ ↦ 1#isize',
    'instance': 'local Discriminant (Option T) Isize, read_discriminant := optionTag',
    'tag_lemmas': ['optionTag_none','optionTag_some'],
    'source_row': {
      'source':'R245 decoded TypeDeclId 3, core::option::Option; R255 is the same LLBC modulo ordered_decls metadata',
      'row_sha256':json.loads(DISCRIMINANT_BINDING.read_text())['type_row_sha256'],
      'row_sha256_definition':'SHA-256 recorded for the exact extracted Option TypeDecl row in option-type-source.json',
      'variant_tags':json.loads(DISCRIMINANT_BINDING.read_text())['variants'],
      'source_row_artifact':str(OPTION_ROW.relative_to(ROOT))},
    'scope':'Explicit discriminator API binding for the source Option variant tags; the three generated bodies are unchanged.'
  },
  'initial_failure': {
    'log':' .r21-scratch/aspis-focus-1790913120788357000.log'.strip(),
    'exit_status':1,
    'diagnostic':'Lean failed to synthesize `Discriminant (Option core.convert.Infallible) ?m.3`; the generated from_residual body constrains the discriminant result against `0#isize`.',
    'log_sha256':sha(FAIL_LOG.read_bytes()),
    'preserved':True
  },
  'lead_reported_success': {
    'log':str(PASS_LOG.relative_to(ROOT)),
    'exit_status':0,
    'log_sha256':sha(PASS_LOG.read_bytes()),
    'campaign_result':'Reported by lead; this generator update does not rerun it.',
    'axiom_output_summary':'optionTag and its two tag lemmas: propext, Classical.choice, Quot.sound; branch: no axioms; from_residual and C.input: propext, Classical.choice, Quot.sound.'
  },
  'pinned_aeneas_source': {
    'excerpt':'pinned-Discriminant.lean',
    'sha256':sha(PINNED_DISCRIMINANT.read_bytes()),
    'module':'Aeneas.Data.Discriminant (pinned source excerpt containing Aeneas.Std.Discriminant and read_discriminant)',
    'source_excerpt_sha256':sha(PINNED_DISCRIMINANT.read_bytes()),
    'prior_note':'Aeneas Data/Discriminant excerpt pin; ControlFlow and Infallible source extraction was not needed for this correction.'
  },
  'shadow_representations_added':0,
  'existing_representation_binding':{
    'B':'AspisR249R110Raw.circle_norm.joined_inverse.line_norm.r110_norm.B (alias Std.U32)',
    'C':'AspisR249R110Raw.circle_norm.joined_inverse.line_norm.r110_norm.C (alias B × B)',
    'CM31':'AspisR156FullFreeze.aspis_core.field.CM31',
    'source_adapter':str(RAW.relative_to(ROOT)),
    'raw_adapter_sha256':sha(raw)},
  'builtin_availability_inventory':{
    'ControlFlow':'The generated declarations use the Aeneas Std ControlFlow type/constructors; the lead-reported successful Lean compile confirms resolution in the pinned build workspace. A separate source excerpt was not needed.',
    'Infallible':'The generated declarations use Aeneas Std Infallible; the lead-reported successful Lean compile confirms resolution in the pinned build workspace. A separate source excerpt was not needed.',
    'read_discriminant':'Pinned Discriminant source exports read_discriminant; the first compile lacked Discriminant (Option Infallible), and the lead-reported successful compile after the local Option instance confirms resolution. No compile was rerun here.',
    'result':'ControlFlow, Infallible, and read_discriminant resolved in the lead-reported green Lean compile log.'},
  'sha256':{'generated_Funs_lean':sha(src_bytes),'R249_raw_adapter':sha(raw),'R245_decoded':sha(R245_DECODED.read_bytes()),'R255_ordered_LLBC':sha(R255_LLBC.read_bytes()),'option_type_source':sha(OPTION_ROW.read_bytes()),'discriminant_binding':sha(DISCRIMINANT_BINDING.read_bytes()),'pinned_Discriminant_source':sha(PINNED_DISCRIMINANT.read_bytes()),'initial_failure_log':sha(FAIL_LOG.read_bytes()),'reported_success_log':sha(PASS_LOG.read_bytes()),'generator':sha(Path(__file__).read_bytes()),'output_lean':sha(TARGET.read_bytes())}}
(OUT/'raw-adapter.json').write_text(json.dumps(report,indent=2)+'\n')
md='''# R259 private input raw staging\n\nCreated `AspisR259PrivateInputRaw.lean` by copying the three requested generated R256 declaration blocks verbatim, including their docstrings and attributes. The block byte hashes are equal and replacement count is zero for each declaration. The scratch file imports `AspisR249R110Raw`, opens the existing raw and R156 namespaces, and adds no B, C, or CM31 shadow representation. Before those bodies, it emits the lead-approved local Option `Discriminant` support from R245 TypeDeclId 3: `None=0#isize`, `Some=1#isize`, plus `optionTag_none` and `optionTag_some`.\n\nThe copied `C::input` and its Option `Try::branch`/`FromResidual::from_residual` helpers preserve the generated `ControlFlow`, `Infallible`, and `read_discriminant` names and control flow. No body was manually changed. The previous failure log records the absent `Discriminant (Option Infallible)` instance; the lead reports the new file compiled green in log `1790913218557130000`. This regeneration records that result and does not rerun compilation.\n\nThe pinned `Aeneas.Data.Discriminant` excerpt and exact R245 Option type row (TypeDeclId 3; None tag 0 and Some tag 1, both signed Isize) are hash-recorded in `raw-adapter.json`. The original compile failed for lack of `Discriminant (Option Infallible)`; the lead reports the generated helpers and C::input compiled after the local instance was added. That compile and its axioms output are recorded from the log and were not rerun here. No compile or build was run during this generator update.\n'''
(OUT/'README.md').write_text(md)
files=[SRC,RAW,R245_DECODED,R255_LLBC,OPTION_ROW,DISCRIMINANT_BINDING,PINNED_DISCRIMINANT,FAIL_LOG,PASS_LOG,Path(__file__),TARGET,OUT/'raw-adapter.json',OUT/'README.md']
(OUT/'SHA256SUMS').write_text(''.join(f'{sha(p.read_bytes())}  {p.relative_to(ROOT)}\n' for p in files))
print(json.dumps({'output':str(TARGET),'blocks':checks,'body_or_attribute_replacements':0},indent=2))
