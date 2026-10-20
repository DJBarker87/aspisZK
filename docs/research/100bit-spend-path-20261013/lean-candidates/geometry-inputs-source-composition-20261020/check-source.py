from pathlib import Path
import hashlib,json,re,subprocess
p=Path(__file__).resolve().parent
j=json.loads((p/'extraction/input/source-pins.json').read_text())
h=lambda b:hashlib.sha256(b).hexdigest()
for name,pin in j['kit_files'].items():assert h((p/'extraction/input'/name).read_bytes())==pin
for c in j['cuts']:
 b=subprocess.check_output(['git','show',j['revision']+':'+c['path']]);frag=(p/'extraction/input/fragments'/(c['name']+'.rs')).read_bytes();assert b[c['start_byte']:c['end_byte_exclusive']]==frag;assert h(frag)==c['sha256']
b=subprocess.check_output(['git','show',j['revision']+':crates/aspis-r1-cost-probe/src/verifier.rs']);assert (p/'extraction/input/fragments/error.rs').read_bytes() in b
clean=lambda s:re.sub(r'^set_option (?:maxHeartbeats|maxRecDepth).*\n','',s,flags=re.M)
r=p/'extraction/generated/AspisR1GeometryInputs'
assert clean((r/'Types.lean').read_text())==(p/'sources/AspisR1GeometryInputs/Types.lean').read_text()
s=clean((r/'Funs.lean').read_text()).replace('import AspisR1GeometryInputs.FunsExternal\n','')
arg='  (queryValues : Std.U32 → Result (core.result.Result ((Array M31 5#usize) × M31) GeometryInputsError))\n'
for n in ['geometry_inputs_indexed_loop.body','geometry_inputs_indexed_loop','geometry_inputs_indexed']:s=s.replace('def '+n+'\n','def '+n+'\n'+arg)
s=s.replace('query_values_entry i1','queryValues i1').replace('geometry_inputs_indexed_loop.body\n      queries','geometry_inputs_indexed_loop.body queryValues\n      queries').replace('geometry_inputs_indexed_loop queries','geometry_inputs_indexed_loop queryValues queries')
assert s==(p/'sources/GeometryInputsExplicitQuery.lean').read_text()
print('frozen byte cuts, candidate input pins and reversible explicit-query Lean adapter: PASS')
