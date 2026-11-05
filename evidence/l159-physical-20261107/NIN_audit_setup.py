from pathlib import Path
import json,hashlib,re,difflib,subprocess
E=Path(__file__).resolve().parent; P=E.parent/'owner-dedupe-20261107'; Z=E.parent/'experiment-law-20261106'
# Same hardened raw walker. Only module/root/file selectors differ in drivers.
for name in ['Driver','ProofDriver']:
 original=(Z/('NHZ_'+name+'.lean')).read_text()
 adapted=original.replace('NHZ_','NIN_')
 (E/('NIN_'+name+'.lean')).write_text(adapted)
 (E/('NIN_'+name+'.diff')).write_text(''.join(difflib.unified_diff(original.splitlines(True),adapted.splitlines(True),fromfile='NHZ_'+name+'.lean',tofile='NIN_'+name+'.lean')))
(E/'NIN_batch.py').write_text((Z/'NHZ_batch.py').read_text().replace('NHZ_','NIN_'))
# Inherited complete root set, plus every new named theorem/definition root.
roots=json.loads((P/'NIM_AUDIT_ROOTS_CORRECTED.json').read_text())['roots']
new=['AspisR1.NIN_Cuts.of_producers','AspisR1.NIN_Cuts.carrier_or_collision',
'AspisR1.NIN_PhysicalInstance.physical_instance','AspisR1.NIN_NativeInstance.from_native',
'AspisR1.NIN_WriterProducer.from_native','AspisR1.NIN_GameProjection.PhysicalRealization',
'AspisR1.NIN_GameProjection.game_fields','AspisR1.NIN_GameProjection.bank_images',
'AspisR1.NIN_GameProjection.external_status_independent']
new+=['AspisR1.NIN_Observer.'+x for x in ['OuterTrace','AdmittedSupport','NestedEvents','CanonicalInput','LiteralFlag','canonical_from_initial','stored_public','outer_from_coverage','nested_from_outer','flag_from_results','accepted_iff','realizes']]
roots=list(dict.fromkeys(new+roots));groups=[roots[i:i+400] for i in range(0,len(roots),400)]
(E/'NIN_AUDIT_ROOTS.json').write_text(json.dumps(dict(roots=roots,new_roots=new,groups=groups,provenance='NIM_AUDIT_ROOTS_CORRECTED plus every NIN named proof/definition; all measured on NIN_COMBINED_IMPORT'),indent=1)+'\n')
(E/'NIN_AUDIT_MODULES.json').write_text(json.dumps([['NIN_COMBINED_IMPORT']for g in groups],indent=1)+'\n')
# Source-derived predecessor baselines plus explicit source imports of new modules.
rows={r['module']:r for l in (P/'NIM_EXPECTED_IMPORTS.jsonl').read_text().splitlines()if (r:=json.loads(l))}
for p in E.glob('NIN_*.lean'):
 imports=['Init']+re.findall(r'^import ([\w.]+)',p.read_text(),re.M)
 rows[p.stem]=dict(module=p.stem,imports=list(dict.fromkeys(imports)),source=str(p),source_sha256=hashlib.sha256(p.read_bytes()).hexdigest(),provenance='source import parser; no loaded import-table inference')
(E/'NIN_EXPECTED_IMPORTS.jsonl').write_text(''.join(json.dumps(rows[k])+'\n'for k in sorted(rows)))
walker=E.parent/'axaudit2-20261102/NEP_WALKER.lean'
(E/'NIN_READONLY_NEP_WALKER.lean.txt').write_bytes(walker.read_bytes())
# All native link inputs are retained, including exact generated hardened walker.
code="""from pathlib import Path
import json,hashlib
p=Path('/home/dombarker/project-offloads/codex-cx-ledger8-cache-20261104/NGJ_native_seed')
print(json.dumps({n:(p/n).read_text()for n in ['NFA_WALKER.c','NFA_MemoryLimit.c']}))
"""
r=subprocess.run(['ssh','-o','ControlMaster=no','-o','ConnectTimeout=15','dombarker@100.108.41.90','python3'],input=code,text=True,capture_output=True);assert r.returncode==0,r.stderr
for n,t in json.loads(r.stdout).items():
 p=E/'NIN_native'/n;p.parent.mkdir(exist_ok=True);p.write_text(t)
(E/'NIN_AUDITOR_PROVENANCE.json').write_text(json.dumps(dict(walker_source=str(walker),walker_sha256=hashlib.sha256(walker.read_bytes()).hexdigest(),walker_identical=True,driver_adaptation='module/root/file selectors only; raw NEP audit unchanged; NFX serialized ownership/import checker unchanged',link_inputs=[dict(path=str(p.relative_to(E)),sha256=hashlib.sha256(p.read_bytes()).hexdigest(),bytes=p.stat().st_size)for p in (E/'NIN_native').glob('*.c')]),indent=1)+'\n')
# Repair own runner: retain exact C inputs, never guess a shared seed at link time.
p=E/'NIN_run.py';s=p.read_text();s=s.replace(" command=[T+'/bin/lake','env','leanc'", " for n in sources[1:]:files[n]=(E/n).read_text()\n command=[T+'/bin/lake','env','leanc'")
p.write_text(s)
print(json.dumps(dict(roots=len(roots),groups=len(groups),new_roots=len(new))))
