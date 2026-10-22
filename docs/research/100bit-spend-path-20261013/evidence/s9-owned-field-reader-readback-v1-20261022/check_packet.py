#!/usr/bin/env python3
from pathlib import Path
import hashlib,json,re,subprocess,sys
p=Path(__file__).resolve().parent
sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest()
m=json.loads((p/'manifest.json').read_text())
assert m['schema']=='focused-extractor-proof-packet-v1' and m['compiled_objects_included'] is False and len(m['entries'])==1
for e in m['entries']:
 r=json.loads((p/e['receipt']).read_text());pre=json.loads((p/e['preflight']).read_text());cmd=json.loads((p/e['command']).read_text());log=(p/e['log']).read_text();s=(p/e['source']).read_text()
 assert e['entry_kind']=='map_theorem' and r==e['launch_metrics'] and r['exit_status']==0 and r['process_swaps']==0
 assert r['watchdog_abort'] is None and r['foreign_lean_samples']==[]
 assert sha(p/e['source'])==e['source_sha256']==r['source_sha256']==pre['source_sha256'] and r['object_sha256']==e['object_sha256']
 assert pre['source_revision']==r['source_revision_at_launch'] and pre['no_dependency_builds'] is True
 assert pre['controller_sha256']=='9b827933f26ff248491bf1fd187e6d43b804686512bd49b8edacf8ea6416fab0'==sha(p/'run_focused.py')
 assert e['direct_imports']==pre['direct_imports']
 assert 'LEAN_PATH='+(p/e['profile']).read_text().strip() in cmd['argv']
 assert '-j1' in cmd['argv'] and cmd['argv'][cmd['argv'].index('-M')+1]=='4400'
 for imp in e['direct_imports'].values(): assert Path(imp['path']).is_file() and sha(Path(imp['path']))==imp['sha256']
 for name,ax in e['theorems'].items():
  reports=re.findall("'"+re.escape(name)+r"' depends on axioms:\s*\[(.*?)\]",log,re.S);assert len(reports)==1
  got=set(re.findall(r'[A-Za-z][A-Za-z0-9_.]*',reports[0]));assert got==set(ax) and got<={'propext','Classical.choice','Quot.sound'}
 uncommented=re.sub(r'/\-.*?\-/','',s,flags=re.S);uncommented=re.sub(r'--[^\n]*','',uncommented)
 assert not re.search(r'\b(sorry|admit|axiom|native_decide)\b',uncommented)
 assert not re.search(r'set_option\s+(max|.*Heartbeats|.*RecDepth)',uncommented)
# Revalidate the exact previously committed byte and limb packets (no recompilation).
byte=p.parent/'s9-owned-from-bytes-map-v1-20261022';limb=p.parent/'s9-owned-from-limbs-map-v1-20261022'
for packet in (byte,limb): subprocess.run([sys.executable,'-B',str(packet/'check_packet.py')],check=True,capture_output=True,text=True)
byteManifest=json.loads((byte/'manifest.json').read_text()); limbManifest=json.loads((limb/'manifest.json').read_text())
byteEntry=byteManifest['entries'][0]
assert m['entries'][0]['direct_imports']['S9OwnedFromBytesMapV1']['sha256']==byteEntry['object_sha256']
limbEntries={e['module']:e for e in limbManifest['entries']}
assert m['entries'][0]['direct_imports']['AspisR1S9FieldOwnedV1.Funs']['sha256']==limbEntries['AspisR1S9FieldOwnedV1.Funs']['object_sha256']
ident=json.loads((p/m['source_identity']).read_text());cut=(p/ident['reference_packet']).resolve()
assert sha(cut/'manifest.json')==ident['sourcecut_manifest_sha256']
def norm_decl(path,start,end):
 t=path.read_text();i=t.index(start);j=t.index(end,i);return re.sub(r'\s+',' ',t[i:j]).strip()
ownedF=limb/'AspisR1S9FieldOwnedV1/Funs/sources/Funs.lean'
for fn in ('from_limbs','from_le_bytes'):
 c=norm_decl(cut/'attempt1/generated/Funs.lean',f'def field.wide_exact.WideExact.{fn}','/--');o=norm_decl(ownedF,f'def field.wide_exact.WideExact.{fn}','/--')
 assert c==o;h=hashlib.sha256(c.encode()).hexdigest();assert h==ident[f'candidate_{fn}_body_sha256']==ident[f'owned_{fn}_body_sha256']
c=norm_decl(cut/'attempt1/generated/Funs.lean','def weights.field','\nend ');o=norm_decl(ownedF,'def weights.field','\nend ')
assert c==o;h=hashlib.sha256(c.encode()).hexdigest();assert h==ident['candidate_weights_field_generated_body_sha256']==ident['owned_weights_field_generated_body_sha256']
tc=norm_decl(cut/'attempt1/generated/Types.lean','structure field.CM31 where','\nend ');to=norm_decl(limb/'AspisR1S9FieldOwnedV1/Types/sources/Types.lean','structure field.CM31 where','\nend ')
assert tc==to;th=hashlib.sha256(tc.encode()).hexdigest();assert th==ident['candidate_core_field_types_sha256']==ident['owned_core_field_types_sha256']
assert ident['weights_field_generated_body_equal'] and ident['from_le_bytes_body_equal'] and ident['from_limbs_body_equal']
for ext in ('*.olean','*.elf','*.so','*.pyc'):assert not list(p.rglob(ext))
for line in (p/'SHA256SUMS').read_text().splitlines():d,rel=line.split('  ',1);assert sha(p/rel)==d,rel
print('PASS: field-reader pins, standard theorem axioms, linked byte/limb packets, normalized source identity, no binaries')
