from pathlib import Path
import json,hashlib
E=Path(__file__).resolve().parent;D=Path('docs/research/100bit-spend-path-20261013/lean');T='/home/dombarker/.elan/toolchains/leanprover--lean4---v4.32.0';B='/home/dombarker/project-offloads/codex-cx-terminal-20261107'
provenance=[]
for number,module in [(33,'CopyActiveMaskBasisFacts'),(34,'CopyActiveMaskBasisRegroup')]:
 raw=(D/(module+'.lean')).read_bytes();p=E/'NJB_dependency_inputs'/(module+'.lean');p.parent.mkdir(exist_ok=True);p.write_bytes(raw)
 x=dict(attempt=f'NJB_L{number:03}',kind='lean',module=module,sources=['NJB_dependency_inputs/'+module+'.lean'],command=[T+'/bin/lake','env','lean','-j1','-M7000','-DElab.async=false','-R','NJB_dependency_inputs','-o','NJB_objects/'+module+'.olean','NJB_dependency_inputs/'+module+'.lean'],timeout=180,env=dict(PATH='/home/dombarker/.cargo/bin:/usr/bin:/bin',LEAN_SYSROOT=T,LEAN_PATH=':'.join([B+'/NJB_objects']+json.loads((E/'NJB_PATHS.json').read_text())),CARGO_TARGET_DIR=B+'/NJB_target',TMPDIR=B+'/NJB_tmp'),deps_fingerprint={},expected_time='Private compile of byte-identical missing unchanged canonical dependency; preserve original module owner')
 (E/(x['attempt']+'.json')).write_text(json.dumps(x,indent=1));provenance.append(dict(module=module,source=str(D/(module+'.lean')),sha256=hashlib.sha256(raw).hexdigest(),private_input=str(p),byte_identical=True))
for mod in ['NJB_ActiveModel','NJB_MaskTable']:
 p=E/(mod+'.lean');p.write_text(p.read_text().replace('import NJB_ActiveRegroup','import CopyActiveMaskBasisRegroup'))
rejected=E/'NJB_rejected';rejected.mkdir(exist_ok=True)
for name in ['NJB_ActiveFacts','NJB_ActiveRegroup']:
 p=E/(name+'.lean')
 if p.exists():p.rename(rejected/(name+'.lean.txt'))
(E/'NJB_CANONICAL_DEPENDENCIES.json').write_text(json.dumps(provenance,indent=1)+'\n')
print('missing unchanged math modules retain canonical owners; prefix-owned duplicate copies excluded')
