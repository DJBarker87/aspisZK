from pathlib import Path
import hashlib, json, re

ROOT = Path(__file__).resolve().parent
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
sha_bytes = lambda b: hashlib.sha256(b).hexdigest()
assert __import__('subprocess').run(['python3', str(ROOT/'check_sourcecut.py')], check=False).returncode == 0
cfg = json.loads((ROOT/'attempt-config.json').read_text())
llbc = ROOT/'runs-charon/helper-projection.llbc'
assert sha(llbc) == 'ed7f5390e7f02eb4466359493567de5989c947975e7277dcacad6fdab747cff3'
obj = json.loads(llbc.read_text())
assert obj.get('has_errors') is False
assert len(obj['translated']['fun_decls']) == 188
assert len(obj['translated']['type_decls']) == 60

# Pin the four source method identities and their LLBC spans/opacity. This is
# source evidence only; it must not silently promote the opaque calls to Lean
# definitions.
owner_map=json.loads((ROOT/'wide-exact-owner-map.json').read_text())
assert owner_map['schema']=='focused-source-owner-comparison-v1'
assert owner_map['classification']=='read-only exact-source comparison; not a Lean refinement theorem'
expected_methods={
 'add':(10,81,88,'711892452ab80cd1a37abcdd41e42375b86d82b577586567da82c5eacadf0f4f'),
 'mul':(11,112,126,'47c8044c02a35cb46e284c30597906a748a2e8904b3ed811189c5f19855b3462'),
 'mul_m31':(9,190,198,'5e7bdbf0090b8501ebfb42f18e59eec33de255c439d40296787301df2736eb69'),
 'mul_qm31':(8,178,186,'617f4bfe9aaaabf3129ada726faaf601dfac8e1d978eb62ba007dcc6032fdf9f'),
}
by_id={x.get('def_id'):x for x in obj['translated']['fun_decls'] if isinstance(x,dict)}
for method,(def_id,start,end,body_hash) in expected_methods.items():
    d=by_id[def_id]; m=d.get('item_meta') or {}; span=(m.get('span') or {}).get('data') or {}
    text=m.get('source_text') or ''
    assert span.get('beg',{}).get('line')==start and span.get('end',{}).get('line')==end,method
    assert m.get('opacity')=='Opaque',method
    assert sha_bytes(text.encode())==body_hash,method
assert len(owner_map['method_comparisons'])==4

def idents(meta):
    return [x['Ident'][0] for x in meta.get('name',[]) if isinstance(x,dict) and 'Ident' in x]
items=[]
for d in obj['translated']['fun_decls']:
    if isinstance(d,dict):
        m=d.get('item_meta') or {}
        items.append((idents(m),m.get('source_text',''),m.get('opacity')))
def one(name_tail, text_fragment=None):
    found=[(names,text,opacity) for names,text,opacity in items if names[-len(name_tail):] == name_tail and (text_fragment is None or text_fragment in text)]
    assert len(found)==1, (name_tail,text_fragment,len(found))
    return found[0]
for name, frag in [
    (['weights','factored_s2_libra_weights'],'fn factored_s2_libra_weights'),
    (['weights','selected_projection'],'pub fn selected_projection'),
    (['weights','field'],'pub fn field(bytes:'),
    (['field','wide_exact','from_le_bytes'],'pub fn from_le_bytes'),
    (['field','mul'],'pub fn mul(self, rhs: QM31)'),
    (['field','square'],'pub fn square(self) -> QM31'),
    (['field','wide_exact','add'],'pub fn add(self, rhs: Self)'),
    (['field','wide_exact','mul'],'pub fn mul(self, rhs: Self)'),
    (['field','wide_exact','mul_m31'],'pub fn mul_m31(self, rhs: M31)'),
    (['field','wide_exact','mul_qm31'],'pub fn mul_qm31'),
    (['weights','twofold_libra_weights'],'fn twofold_libra_weights'),
]:
    names,text,opacity=one(name,frag)
    expected='Opaque' if name in [
      ['field','mul'],['field','square'],
      ['field','wide_exact','add'],['field','wide_exact','mul'],
      ['field','wide_exact','mul_m31'],['field','wide_exact','mul_qm31'],
      ['weights','twofold_libra_weights']] else 'Transparent'
    assert opacity==expected,(name,opacity,expected)

# Generated Aeneas text is retained as diagnostic output, never imported into
# the accepted Lean proof tree. Pin its contents and the successful receipts.
gen=ROOT/'runs-aeneas/generated/AspisR1S9ActualFieldTypesCutV1'
expected_generated={
 'Types.lean':'398a4dab068fe38601e64f09e6e23d627226dc94620bf11cce8e22fc6c013835',
 'Funs.lean':'0d98ec465c2da6b8f6eadcdf4a917352ab4b6b82b21b134cf83c46b6ee59b230',
 'FunsExternal_Template.lean':'08c044ee1b5e7fe0f3da8099c56d24c1936a6b9facdf8d8a3fa3546cc2ce9232',
}
for f,h in expected_generated.items(): assert sha(gen/f)==h,(f,sha(gen/f))
for phase in ('charon','aeneas'):
    r=json.loads((ROOT/f'runs-{phase}/receipt.json').read_text())
    assert r['exit_status']==0 and r['timed_out'] is False
    assert r['limits']=={'memory.high':'2147483648','memory.max':'4294967296','memory.swap.max':'0'}
    assert r['swap_current_bytes']==0 and 'oom_kill 0' in r['memory_events_after']
    assert r['cgroup'] and r['argv']

# This evidence packet deliberately excludes compiled artifacts and transient
# Python caches. Raw Aeneas Lean text is kept only as diagnostics.
for p in ROOT.rglob('*'):
    if p.is_dir():
        assert p.name!='__pycache__',p
    elif p.suffix in ('.pyc','.olean','.ilean'):
        raise AssertionError(f'compiled/cache artifact in source packet: {p}')

# Structural comparison to the previous Pair adapter. This intentionally
# checks normalized generated-body text only; it does not prove a Lean map.
actual_funs=(gen/'Funs.lean').read_text()
pair_dir=ROOT.parents[2]/'docs/research/100bit-spend-path-20261013/lean-candidates/s9-pair-caller-step-adapter-v1-20261022/draft2/sources/AspisR1S9PairCallerStepV1'
pair_funs=(pair_dir/'Funs.lean').read_text()
def get_def(s,name):
    m=re.search(r'(?m)^def '+re.escape(name)+r'\b',s); assert m,name
    e=re.search(r'(?m)^/-- ',s[m.end():])
    z=s[m.start():m.end()+e.start() if e else len(s)]
    z=re.sub(r'(?m)^--.*$','',z)
    z=z.replace('field.wide_exact.WideExact','field.WideExact')
    return re.sub(r'\s+','',z)
for name in ('weights.factored_s2_libra_weights_loop.body','weights.Weights.scalar_factor','weights.factored_s2_libra_weights'):
    assert get_def(actual_funs,name)==get_def(pair_funs,name),name

print('attempt7 extraction checks: PASS (source/LLBC/Aeneas evidence only)')
