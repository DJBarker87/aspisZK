from pathlib import Path
import json,re,shutil,hashlib
b=Path('/tmp/root-m31-inverse-lean-v1-20261020');raw=Path('/tmp/root-geometry-inputs-extraction-v2-20261020/generated/AspisR1GeometryInputs');w=Path('/tmp/root-geometry-inputs-lean-v1-20261020');w.mkdir();(w/'sources/AspisR1GeometryInputs').mkdir(parents=True);clean=lambda s:re.sub(r'^set_option (?:maxHeartbeats|maxRecDepth).*\n','',s,flags=re.M);(w/'sources/AspisR1GeometryInputs/Types.lean').write_text(clean((raw/'Types.lean').read_text()));s=clean((raw/'Funs.lean').read_text()).replace('import AspisR1GeometryInputs.FunsExternal\n','');
arg='  (queryValues : Std.U32 → Result (core.result.Result ((Array M31 5#usize) × M31) GeometryInputsError))\n'
for n in ['geometry_inputs_indexed_loop.body','geometry_inputs_indexed_loop','geometry_inputs_indexed']:
 s=s.replace('def '+n+'\n','def '+n+'\n'+arg)
s=s.replace('query_values_entry i1','queryValues i1').replace('geometry_inputs_indexed_loop.body\n      queries','geometry_inputs_indexed_loop.body queryValues\n      queries').replace('geometry_inputs_indexed_loop queries','geometry_inputs_indexed_loop queryValues queries');(w/'sources/GeometryInputsExplicitQuery.lean').write_text(s)
c=json.loads((b/'config.json').read_text());c['unit']=w.name;c['source_revision']='c8ea8dd49 indexed geometry input-loop CANDIDATE; only explicit per-query helper boundary, unchanged emitted Vec/array/controlflow';c['stages']=[]
for ph,n,sp,im in [('types','AspisR1GeometryInputs.Types','AspisR1GeometryInputs/Types.lean',{}),('body','GeometryInputsExplicitQuery','GeometryInputsExplicitQuery.lean',{'AspisR1GeometryInputs.Types':'FROM_STAGE_types'})]:c['stages'].append(dict(phase=ph,module=n,source='sources/'+sp,source_sha256=hashlib.sha256((w/'sources'/sp).read_bytes()).hexdigest(),direct_imports=im))
(w/'config.json').write_text(json.dumps(c,indent=2)+'\n')
for n in ['run-stage.py','run-admitted.py']:shutil.copy(b/n,w/n)
