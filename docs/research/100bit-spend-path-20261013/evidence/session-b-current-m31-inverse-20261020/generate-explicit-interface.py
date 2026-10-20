from pathlib import Path
import json,re,shutil,hashlib
b=Path('/tmp/root-r17-domain-canonical-v2-20261020');raw=Path('/tmp/root-m31-inverse-extraction-v1-20261020/generated/AspisR1M31Inverse');w=Path('/tmp/root-m31-inverse-lean-v1-20261020');w.mkdir();(w/'sources/AspisR1M31Inverse').mkdir(parents=True);clean=lambda s:re.sub(r'^set_option (?:maxHeartbeats|maxRecDepth).*\n','',s,flags=re.M);t=w/'sources/AspisR1M31Inverse/Types.lean';t.write_text(clean((raw/'Types.lean').read_text()));s=clean((raw/'Funs.lean').read_text()).replace('import AspisR1M31Inverse.FunsExternal\n','');
for name in ['field.square_n_loop.body','field.square_n_loop','field.square_n']:
 # The loop name is also prefix of .body; replace exact declaration token only.
 s=s.replace('def '+name+'\n','def '+name+'\n  (mul : field.M31 → field.M31 → Result field.M31)\n')
s=s.replace('def field.M31.inv (self : field.M31)','def field.M31.inv (mul : field.M31 → field.M31 → Result field.M31) (self : field.M31)');s=s.replace('field.M31.mul','mul');s=s.replace('field.square_n_loop.body iter1','field.square_n_loop.body mul iter1');s=s.replace('field.square_n_loop { start','field.square_n_loop mul { start');s=s.replace('field.square_n t','field.square_n mul t');(w/'sources/M31InverseExplicitMul.lean').write_text(s)
c=json.loads((b/'config.json').read_text());c['unit']=w.name;c['source_revision']='c8ea8dd49 exact M31 inv/square_n bodies; only explicit multiplication interface, default resource settings';c['stages']=[]
for phase,n,sp,im in [('types','AspisR1M31Inverse.Types','AspisR1M31Inverse/Types.lean',{}),('body','M31InverseExplicitMul','M31InverseExplicitMul.lean',{'AspisR1M31Inverse.Types':'FROM_STAGE_types'})]:c['stages'].append(dict(phase=phase,module=n,source='sources/'+sp,source_sha256=hashlib.sha256((w/'sources'/sp).read_bytes()).hexdigest(),direct_imports=im))
(w/'config.json').write_text(json.dumps(c,indent=2)+'\n')
for n in ['run-stage.py','run-admitted.py']:shutil.copy(b/n,w/n)
print(w)
