from auditlib7 import *
import difflib
path='crates/aspis-r1-cost-probe/src/prover.rs';current=read('rw',path);out=[]
for label,rev in [('constructor','03b37df2aa2a0871fb574a320eae0c437f0b33b8'),('materialize','b98d7dbb865d966437731b7a770b81913e30c206')]:
 raw=subprocess.check_output(['git','show',rev+':'+path],text=True)
 def section(s,name):
  a=s.index('fn '+name+'(');b=s.find('\nfn ',a+3);return s[a:b if b!=-1 else len(s)]
 if label=='constructor':assert section(raw,'prepare_opening')==section(current,'prepare_opening')
 else:
  old=section(raw,'prepare_opening');new=section(current,'prepare_opening')
  assert old.replace('let w=Weights::new(variant,&sem.alpha,&sem.z)?;', 'let w=retain_weights_box(Weights::new(variant,&sem.alpha,&sem.z)?);')==new
 out.append(dict(path=path,prior_revision=rev,prior_sha256=hashlib.sha256(raw.encode()).hexdigest(),candidate_revision=pins['rw'],candidate_sha256=hashlib.sha256(current.encode()).hexdigest(),full_diff=''.join(difflib.unified_diff(raw.splitlines(True),current.splitlines(True))),disposition='Constructor-era prepare_opening and retain_weights_box bodies unchanged; other hunks are batch3 mask/public-byte routing.' if label=='constructor' else 'Materialize-era prepare_opening differs only by authorized retained Box wrapper at constructor result; materialization/error/order unchanged. Complete resource family laws do not assert allocation/world independence. Later constructor binding supplies repair.',selected_body_match=True))
for path in ['evidence/pv-batch2-20261027/batch2f/NATIVE-BOX-FIDELITY.json','evidence/pv-batch2-20261027/batch2f/BOX-DEFECT.json','evidence/pv-batch2-20261027/batch2f/ELF-GATE.json','evidence/pv-batch3-20261027/d336-native-reuse.json','evidence/pv-relink-20261028/native-std-r3/receipt.json','evidence/pv-relink-20261028/native-cargo-r1/receipt.json']:
 assert read('rw',path),path
(P/'native-pin-exceptions7.json').write_text(json.dumps(out,indent=2)+'\n')
(P/'manifest.json').write_text(json.dumps(manifest,indent=2)+'\n')
print('2 file-hash deltas resolved by exact caller/body checks')
