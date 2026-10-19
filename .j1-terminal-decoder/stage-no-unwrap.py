from pathlib import Path
import hashlib, json, shutil, re

revision = 'b330ade02e82770977de48471ee0d0b886c0e796'
orig = Path('.j1-terminal-decoder/no-unwrap')
receipt = json.loads((orig / 'aeneas-receipt.json').read_text())
assert receipt['exit_status'] == 0 and receipt['source_revision'] == revision
assert receipt['swaps'] == 0
assert receipt['limits'] == {'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0'}
raw = (orig / 'TerminalDecoder-renamed.llbc').read_bytes()
assert hashlib.sha256(raw).hexdigest() == 'afc5671dea49dcf3531a8f47310b610c4ab288eba235ebf1a138a8181eda07f2'
llbc = json.loads(raw)
assert not llbc['has_errors']
option = next(t for t in llbc['translated']['type_decls'] if t and t['def_id'] == 20)
assert [(v['name'],v['discriminant']) for v in option['kind']['Enum']] == [
    ('None',{'Scalar':{'Signed':['Isize','0']}}),
    ('Some',{'Scalar':{'Signed':['Isize','1']}})]
lean = Path('docs/research/100bit-spend-path-20261013/lean')
dst = lean / 'extracted-terminal-decoder-20261016/AspisR1TerminalDecoder'
dst.mkdir(parents=True,exist_ok=True)
for name in ('Types.lean','Funs.lean'):
    data = (orig / name).read_bytes()
    assert b'Slice.Insts.CoreCmpPartialEqArray.eq' not in data
    assert not re.search(rb'(?m)^\s*(axiom|opaque|sorry|admit)\b',data)
    shutil.copy2(orig / name, dst / name)
assert b'core.result.Result.unwrap' not in (orig / 'Funs.lean').read_bytes()
compat = (lean/'extracted-adapter-reconstruct-20261016/AspisR1AdapterReconstruct/FunsExternal.lean').read_text()
compat = compat.replace('AspisR1AdapterReconstruct','AspisR1TerminalDecoder')
compat = compat.replace('Exact adapter extraction-a LLBC (171b46ec...4ad2c1d), type 7:',
                        'Exact decoder renamed LLBC (afc5671d...da07f2), type 20:')
(dst/'FunsExternal.lean').write_text(compat)
functions = [x for x in re.findall(r'\bdef\s+([\w.]+)',(orig/'Funs.lean').read_text())
             if ('decode' in x or x.endswith('M31.from_le_bytes'))
             and '.closure' not in x and not x.endswith('.body')]
assert len(functions) == 15
audit = lean/'TerminalDecoderGeneratedAudit.lean'
audit.write_text('import AspisR1TerminalDecoder.Funs\n\n'+''.join(
    '#print axioms AspisR1TerminalDecoder.'+f+'\n' for f in functions))
proof = Path('.j1-terminal-decoder/no-unwrap-proofs')
(proof/'sources').mkdir(parents=True,exist_ok=True)
manifest = {'format':2,'modules':{},'topological_order':[],'groups':{}}
for name,path,imports,count in [
    ('AspisR1TerminalDecoder.Types',dst/'Types.lean',['Aeneas'],0),
    ('AspisR1TerminalDecoder.FunsExternal',dst/'FunsExternal.lean',['Aeneas','AspisR1TerminalDecoder.Types'],2),
    ('AspisR1TerminalDecoder.Funs',dst/'Funs.lean',['Aeneas','AspisR1TerminalDecoder.Types','AspisR1TerminalDecoder.FunsExternal'],0),
    ('TerminalDecoderGeneratedAudit',audit,['AspisR1TerminalDecoder.Funs'],15)]:
    rel = name.replace('.','/')+'.lean'
    stage = proof/'sources'/rel
    stage.parent.mkdir(parents=True,exist_ok=True)
    shutil.copy2(path,stage)
    manifest['modules'][name] = {'source':str(path),'source_sha256':hashlib.sha256(path.read_bytes()).hexdigest(),
        'source_revision':revision,'imports':imports,'stage_as':rel,
        'role':'Unchanged no-unwrap decoder emission or scoped builtin tag/audit companion; no decoder correctness claim',
        'axiom_requests':count}
    manifest['topological_order'].append(name)
(proof/'sources/SOURCE-MANIFEST.json').write_text(json.dumps(manifest,indent=2)+'\n')
shutil.copy2('.j1-adapter-reconstruct/proofs/runner.py',proof/'runner.py')
print(json.dumps(manifest,indent=2))
