#!/usr/bin/env python3
import hashlib,json,re
from pathlib import Path
ROOT=Path(__file__).resolve().parent
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def need(c,m):
    if not c: raise SystemExit('FAIL: '+m)
pins={
 'source-pins/Funs.lean':'b3aa665deadedac1f04233f5535bce0774cfed34e6ee7f979657982504d97c2b',
 'source-pins/Types.lean':'e48b04f110817ce911f9f2471266a92a2244fa4f2154ef2b272359a49b52dd5b',
 'source-pins/FunsExternal_Template.lean':'403908f4fa4001a8842fa219fe0da2c7af9a435a3bdf0d0830e6e8de77d545b2',
 'source-pins/tx2_common.rs':'9e927542736d60330cea204a54c4b9b923a29d7351da7b664a74eb21c854a300',
}
for f,h in pins.items(): need(sha(ROOT/f)==h,'source pin '+f)
funs=(ROOT/'source-pins/Funs.lean').read_text()
start=funs.index('def verifier.candidate.tx2_common\n')
next_decl=re.search(r'^/-- \[aspis_r1_cost_probe::verifier::candidate::tx2_authenticated\]',funs[start:],re.M)
need(next_decl is not None,'structural end for generated tx2_common')
block=funs[start:start+next_decl.start()]
need('  := do\n' in block,'source body marker')
source_body=block.split('  := do\n',1)[1]
cut=(ROOT/'sources/S4Tx2FullSourceOwnedCutV1.lean').read_text()
a=cut.index('def tx2CommonFullSourceCut')
body_start=cut.index(' := do\n',a)+len(' := do\n')
b=cut.index('\n\nprivate theorem branch_continue_inv',body_start)
cut_body=cut[body_start:b]+'\n'
subs=json.loads((ROOT/'source-pins/substitutions.json').read_text())
for old,new in subs: source_body=source_body.replace(old,new)
tokens=lambda s: re.findall(r'[A-Za-z0-9_]+|[^\sA-Za-z0-9_]',s)
need(tokens(source_body)==tokens(cut_body),'complete generated body differs after declared substitutions')
# Confirm exact external signatures used by replacement slots.
ext=(ROOT/'source-pins/FunsExternal_Template.lean').read_text()
flat=' '.join(ext.split())
need('axiom core.option.Option.ok_or {T : Type} {E : Type} : (Option T) → E → Result (core.result.Result T E)' in flat,
     'Option.ok_or template signature')
need('axiom aspis_core.field.wide_exact.WideExact.from_le_bytes : (Slice Std.U8) → Result (Option aspis_core.field.wide_exact.WideExact)' in flat,
     'WideExact.from_le_bytes template signature')
need('axiom weights.powers (N : Std.Usize) : aspis_core.field.wide_exact.WideExact → Result (Array aspis_core.field.wide_exact.WideExact N)' in flat,
     'weights.powers template signature')
need('optionOkOr : {T E : Type} → Option T → E → Result (core.result.Result T E)' in cut,
     'typed Option.ok_or slot')
need('wideFromLeBytes : Slice Std.U8 → Result (Option Wide)' in cut,
     'typed from_le_bytes slot')
need('weightsPowers : Std.Usize → Wide → Result (Array Wide 29#usize)' in cut,
     'typed powers slot')
need(cut.count('ControlFlow.Break residual')==6,'all emitted residual paths retained')
need('ops.finishRelation' in cut and 'deref_mut_back s4' in cut,'inline full suffix retained')
need('tx2CommonFullSourceCut_success_reaches_query_loop' in cut,'full-body success inversion theorem present')
need('a.next = ops.split' in cut,'split guard equality retained in success witness')
need('sorry' not in cut,'no sorry in candidate source')
print('PASS: pinned source, exact complete-body token equality after declared callee/constant substitutions, external signatures, all residual branches and suffix')
