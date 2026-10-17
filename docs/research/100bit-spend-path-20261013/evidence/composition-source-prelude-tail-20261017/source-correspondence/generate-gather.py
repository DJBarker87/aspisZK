from pathlib import Path
import re, hashlib, json
base = Path('/Users/dominic/ZK/.worktrees/100bit-spend-path/docs/research/100bit-spend-path-20261013/evidence/terminal-indexed-source-candidate-20261016')
funs, types = base/'Funs.lean', base/'Types.lean'
expected = {'Funs.lean':'04fc129bbd54c8792d5c11e6c017e810cfc68d7a4a9577eca9455088ed04a42e',
            'Types.lean':'60cf4b447bc2e9d57d58fc2b1386e91120fa6fb26961e725690ac09da4ac6713'}
for p in (funs, types):
    got=hashlib.sha256(p.read_bytes()).hexdigest()
    if got != expected[p.name]: raise SystemExit(f'{p}: {got} != pinned {expected[p.name]}')
def blocks(path): return re.split(r'(?=/--)', path.read_text())
def select(blks,name):
    matches=[b for b in blks if re.search(r'\bdef\s*\n?\s*'+re.escape(name)+r'(?=\s|\n|:)',b)]
    if len(matches)!=1: raise SystemExit(f'{name}: expected 1 block, got {len(matches)}')
    return matches[0].rstrip()
fnblocks,tyblocks=blocks(funs),blocks(types)
closures=[f'pool_v1.pair_forest_semantic_terminal.composition_parts.closure_{i}' for i in range(1,5)]
selected_types=[select(tyblocks,n) for n in closures]
core_names=['field.QM31.Insts.CoreCloneClone.clone','field.QM31.Insts.CoreCloneClone','field.QM31.Insts.CoreMarkerCopy']
selected_funs=[select(fnblocks,n) for n in core_names]
for n in closures:
    for suf in ['.Insts.CoreOpsFunctionFnMutTupleUsizeQM31.call_mut',
                '.Insts.CoreOpsFunctionFnOnceTupleUsizeQM31.call_once',
                '.Insts.CoreOpsFunctionFnOnceTupleUsizeQM31',
                '.Insts.CoreOpsFunctionFnMutTupleUsizeQM31']:
        selected_funs.append(select(fnblocks,n+suf))
# Put the copied exact declarations in a fresh namespace to avoid colliding with
# stale cached generated Funs. Preserve external selected_claim identity.
cut='AspisR1CompositionPartsGatherCut'
def adapt(s):
    s=s.replace('pool_v1.pair_forest_semantic_terminal.POOL_V1_PAIR_FOREST_TERMINAL_C1_COLUMNS_V1',
                'AspisR1SelectedMaskProbe.pool_v1.pair_forest_semantic_terminal.POOL_V1_PAIR_FOREST_TERMINAL_C1_COLUMNS_V1')
    s=s.replace('pool_v1.pair_forest_semantic_terminal.selected_claim',
                'AspisR1SelectedMaskProbe.pool_v1.pair_forest_semantic_terminal.selected_claim')
    for n in closures:
        s=s.replace(n, cut+'.'+n)
    s=s.replace('field.QM31.Insts.CoreCloneClone', cut+'.field.QM31.Insts.CoreCloneClone')
    s=s.replace('field.QM31.Insts.CoreMarkerCopy', cut+'.field.QM31.Insts.CoreMarkerCopy')
    return s
header='''import SelectedClaimProofs
/-! Minimal exact generated source cut for `composition_parts` closure gathers.
Source blocks are copied from sealed candidate Funs/Types pins listed in
`source-map.json`; declarations are relocated under a fresh namespace to avoid
stale-object collisions. -/
set_option autoImplicit false
open Aeneas Aeneas.Std Result
open AspisR1SelectedMaskProbe
'''
out=Path('/tmp/CompositionPartsGatherSlice-20261017/CompositionPartsGatherSlice.lean')
out.write_text(header+'\n\n'.join(adapt(s) for s in selected_types+selected_funs)+'\n')
# Verify the current sealed callback bodies against the earlier checked G slice.
oldfuns=Path('/Users/dominic/ZK/.worktrees/100bit-spend-path/docs/research/100bit-spend-path-20261013/evidence/terminal-qm31-extraction-20261016/attempt-fromfn-copy-indexed/output/generated/AspisR1SelectedMaskProbe/Funs.lean')
old_sha='76abaf4cdd807726983f944b9e4710044f49e0a8a006ea1bdfd553fb00e3cc5c'
if hashlib.sha256(oldfuns.read_bytes()).hexdigest()!=old_sha: raise SystemExit('old callback pin mismatch')
def token_block(path,name):
    matches=[b for b in blocks(path) if re.search(r'\bdef\s*\n?\s*'+re.escape(name)+r'(?=\s|\n|:)',b)]
    if len(matches)!=1: raise SystemExit(f'{path}: {name}: expected one block, got {len(matches)}')
    x=re.sub(r'/\*.*?\*/','',matches[0],flags=re.S)
    x=re.sub(r'/-.*?-/','',x,flags=re.S)
    x=re.sub(r'--[^\n]*','',x)
    return re.sub(r'\s+','',x)
callback_checks=[]
for n in closures:
    name=n+'.Insts.CoreOpsFunctionFnMutTupleUsizeQM31.call_mut'
    a,b=token_block(oldfuns,name),token_block(funs,name)
    if a!=b: raise SystemExit(f'callback token mismatch: {name}')
    callback_checks.append({'name':name,'token_sha256':hashlib.sha256(a.encode()).hexdigest(),'old_and_current_token_identical':True})
# record a reversible name-only map for each declaration block
mapping=[]
for n in closures:
    mapping.append({'source_type':n,'cut_type':cut+'.'+n})
    for suf in ['.Insts.CoreOpsFunctionFnMutTupleUsizeQM31.call_mut','.Insts.CoreOpsFunctionFnOnceTupleUsizeQM31.call_once','.Insts.CoreOpsFunctionFnOnceTupleUsizeQM31','.Insts.CoreOpsFunctionFnMutTupleUsizeQM31']:
        mapping.append({'source_fun':n+suf,'cut_fun':cut+'.'+n+suf})
for n in core_names: mapping.append({'source_fun':n,'cut_fun':cut+'.'+n})
manifest={'source_Funs_sha256':expected['Funs.lean'],'source_Types_sha256':expected['Types.lean'],'source_files':{'Funs':str(funs),'Types':str(types),'prior_checked_Funs':str(oldfuns)},'prior_checked_Funs_sha256':old_sha,'callback_body_token_checks':callback_checks,'copied_declarations':mapping,'output_sha256':hashlib.sha256(out.read_bytes()).hexdigest(),'selected_claim_reference':'AspisR1SelectedMaskProbe.pool_v1.pair_forest_semantic_terminal.selected_claim','transformation':'namespace relocation of closure/copy declarations; selected_claim explicitly qualified to its retained owner; declaration bodies otherwise copied verbatim'}
Path('/tmp/CompositionPartsGatherSlice-20261017/source-map.json').write_text(json.dumps(manifest,indent=2)+'\n')
print(manifest['output_sha256'])
