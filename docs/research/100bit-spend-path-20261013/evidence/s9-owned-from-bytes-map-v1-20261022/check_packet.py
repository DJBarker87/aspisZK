#!/usr/bin/env python3
from pathlib import Path
import hashlib, json, re, subprocess, sys
p = Path(__file__).resolve().parent
sha = lambda f: hashlib.sha256(f.read_bytes()).hexdigest()
m = json.loads((p / 'manifest.json').read_text())
assert m['schema'] == 'focused-extractor-proof-packet-v1' and m['compiled_objects_included'] is False
assert len(m['entries']) == 1
for e in m['entries']:
    r=json.loads((p/e['receipt']).read_text()); pre=json.loads((p/e['preflight']).read_text()); cmd=json.loads((p/e['command']).read_text()); log=(p/e['log']).read_text(); s=(p/e['source']).read_text()
    assert e['entry_kind']=='map_theorem' and r==e['launch_metrics'] and r['exit_status']==0 and r['process_swaps']==0
    assert r['watchdog_abort'] is None and r['foreign_lean_samples']==[]
    assert sha(p/e['source'])==e['source_sha256']==r['source_sha256']==pre['source_sha256'] and r['object_sha256']==e['object_sha256']
    assert pre['source_revision']==r['source_revision_at_launch'] and pre['no_dependency_builds'] is True
    assert pre['controller_sha256']== '9b827933f26ff248491bf1fd187e6d43b804686512bd49b8edacf8ea6416fab0' == sha(p/'run_focused.py')
    assert e['direct_imports']==pre['direct_imports']
    assert 'LEAN_PATH='+ (p/e['profile']).read_text().strip() in cmd['argv']
    assert '-j1' in cmd['argv'] and cmd['argv'][cmd['argv'].index('-M')+1]=='4400'
    for imp in e['direct_imports'].values():
        assert Path(imp['path']).is_file() and sha(Path(imp['path']))==imp['sha256']
    for name,ax in e['theorems'].items():
        reports=re.findall("'"+re.escape(name)+r"' depends on axioms:\s*\[(.*?)\]",log,re.S)
        assert len(reports)==1
        got=set(re.findall(r'[A-Za-z][A-Za-z0-9_.]*',reports[0]))
        assert got==set(ax) and got <= {'propext','Classical.choice','Quot.sound'}
    uncommented=re.sub(r'/\-.*?\-/','',s,flags=re.S);uncommented=re.sub(r'--[^\n]*','',uncommented)
    assert not re.search(r'\b(sorry|admit|axiom|native_decide)\b',uncommented)
    assert not re.search(r'set_option\s+(max|.*Heartbeats|.*RecDepth)',uncommented)

# Reuse and independently verify the prior limb-map packet, without recompiling it.
limb=p.parent/'s9-owned-from-limbs-map-v1-20261022'
subprocess.run([sys.executable,'-B',str(limb/'check_packet.py')],check=True,capture_output=True,text=True)
lm=json.loads((limb/'manifest.json').read_text())
limb_entries={e['module']:e for e in lm['entries']}
for dep in m['reused_dependencies']:
    linked=(p/dep['packet']).resolve(); assert linked.is_file()
    e=limb_entries[dep['module']]
    assert e['object_sha256']==dep['object_sha256']
# Verify the three exact imported owners from the selected profile, including the reusable limb object.
expected={'S9OwnedFromLimbsMapV1':limb_entries['S9OwnedFromLimbsMapV1']['object_sha256'],
          'AspisR1S9FieldOwnedV1.Funs':limb_entries['AspisR1S9FieldOwnedV1.Funs']['object_sha256']}
for imp, ref in expected.items(): assert m['entries'][0]['direct_imports'][imp]['sha256']==ref

# Verify normalized copied definitions against committed source-cut extraction.
ident=json.loads((p/m['source_identity']).read_text());cut=(p/ident['reference_packet']).resolve()
assert sha(cut/'manifest.json')==ident['sourcecut_manifest_sha256']
def norm_decl(path,start,end):
    t=path.read_text();i=t.index(start);j=t.index(end,i);return re.sub(r'\s+',' ',t[i:j]).strip()
for fn in ('from_limbs','from_le_bytes'):
    c=norm_decl(cut/'attempt1/generated/Funs.lean',f'def field.wide_exact.WideExact.{fn}','/--')
    o=norm_decl(limb/'AspisR1S9FieldOwnedV1/Funs/sources/Funs.lean',f'def field.wide_exact.WideExact.{fn}','/--')
    assert c==o
    h=hashlib.sha256(c.encode()).hexdigest()
    assert h==ident[f'candidate_{fn}_body_sha256']==ident[f'owned_{fn}_body_sha256']
tc=norm_decl(cut/'attempt1/generated/Types.lean','structure field.CM31 where','\nend ')
to=norm_decl(limb/'AspisR1S9FieldOwnedV1/Types/sources/Types.lean','structure field.CM31 where','\nend ')
assert tc==to
th=hashlib.sha256(tc.encode()).hexdigest();assert th==ident['candidate_core_field_types_sha256']==ident['owned_core_field_types_sha256']
for ext in ('*.olean','*.elf','*.so','*.pyc'): assert not list(p.rglob(ext))
for line in (p/'SHA256SUMS').read_text().splitlines():
    digest,rel=line.split('  ',1);assert sha(p/rel)==digest,rel
print('PASS: source/command/import pins, standard theorem axioms, reused limb packet, normalized source-body identity, no binaries')
