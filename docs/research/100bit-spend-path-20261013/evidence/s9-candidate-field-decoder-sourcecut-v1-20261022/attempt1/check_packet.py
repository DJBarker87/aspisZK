from pathlib import Path
import hashlib, json, subprocess

ROOT=Path(__file__).resolve().parent
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
subprocess.run(['python3',str(ROOT.parent/'check_sourcecut.py')],check=True)
for phase in ('charon','aeneas'):
    receipt=json.loads((ROOT/'runs'/phase/'receipt.json').read_text())
    reservation=json.loads((ROOT/'admission'/f'reservation-{phase}.json').read_text())
    assert receipt['exit_status']==0 and not receipt['timed_out'],phase
    assert receipt['swap_current_bytes']==0
    assert reservation['limits']=={'memory.high':'2147483648','memory.max':'4294967296','memory.swap.max':'0'}
    events={k:int(v) for k,v in (line.split() for line in receipt['memory_events_after'].splitlines())}
    assert all(events.get(k,0)==0 for k in ('max','oom','oom_kill','oom_group_kill'))
    assert all(json.loads((ROOT/'admission'/f'admission-{phase}.json').read_text())['checks'].values())
llbc=ROOT/'runs/charon/field-decoder.llbc'
assert sha(llbc)==sha(ROOT/'field-decoder.llbc')
obj=json.loads(llbc.read_text()); assert obj['has_errors'] is False
tr=obj['translated']; assert obj['charon_version']=='0.1.223'
def name(parts):
    out=[]
    for p in parts or []:
        if 'Ident' in p: out.append(p['Ident'][0])
        elif 'Impl' in p: out.append('{impl}')
        else: out.append(str(p))
    return '::'.join(out)
funs={name(d['item_meta'].get('name')):d for d in tr['fun_decls'] if d and d.get('item_meta')}
targets={
 's9_field_decoder_sourcecut::weights::field':('src/lib.rs',),
 's9_field_decoder_sourcecut::field::wide_exact::{impl}::from_le_bytes':('src/field/wide_exact.rs',),
 's9_field_decoder_sourcecut::field::wide_exact::{impl}::from_limbs':('src/field/wide_exact.rs',),
}
for n,files in targets.items():
 d=funs[n]; m=d['item_meta']
 assert m['opacity']=='Transparent' and d.get('src')=='TopLevel',n
 assert m['source_text'] is not None and m['span']['data']['file_id'] is not None,n
 f=tr['files'][m['span']['data']['file_id']]['name']['Local']
 assert f in files,(n,f)
assert funs['s9_field_decoder_sourcecut::weights::field']['item_meta']['source_text'].encode()==__import__('re').search(r'pub fn field\(bytes:&\[u8\],i:usize\)->E \{ E::from_le_bytes\(&bytes\[i\*32\.\.\(i\+1\)\*32\]\)\.unwrap\(\) \}',(ROOT.parent/'input/src/lib.rs').read_text()).group(0).encode()
foreign={n for n,d in funs.items() if d['item_meta']['opacity']=='Foreign'}
expected={
 'core::slice::index::{impl}::index',
 'core::option::{impl}::unwrap',
 'core::slice::{impl}::len',
 'core::num::{impl}::from_le_bytes',
}
assert expected.issubset(foreign),sorted(expected-foreign)
funslean=(ROOT/'generated/Funs.lean').read_text()
for sym in ('def weights.field','def field.wide_exact.WideExact.from_le_bytes','def field.wide_exact.WideExact.from_limbs','core.num.U32.from_le_bytes','core.option.Option.unwrap','core.slice.index.Slice.index'):
    assert sym in funslean,sym
assert 'unreachable!' not in (ROOT.parent/'input/src/field/wide_exact.rs').read_text()
assert 'unreachable!' not in (ROOT.parent/'input/src/lib.rs').read_text()
print('packet checks: PASS')
