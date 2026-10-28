from pathlib import Path
import subprocess,tarfile,io,json,re
E=Path('evidence/pv-batch2-20261027/batch2f');D='/home/dombarker/project-offloads/codex-pv-batch2-20261027'
code='''from pathlib import Path
import tarfile,sys
D=Path(DIR)
with tarfile.open(fileobj=sys.stdout.buffer,mode='w|') as t:
 for root in [D/'candidate/batch2f-box-native-001',D/'batch2f-box-native-001']:
  for p in root.rglob('*'):
   if p.is_file() and p.suffix in ['.json','.log','.txt']:t.add(p,arcname=str(p.relative_to(D)),recursive=False)
'''.replace('DIR',repr(D))
r=subprocess.run(['ssh','dombarker@100.108.41.90','python3 -'],input=code.encode(),capture_output=True,check=True)
with tarfile.open(fileobj=io.BytesIO(r.stdout)) as t:t.extractall(E,filter='data')
p=E/'candidate/batch2f-box-native-001/receipt';rec=json.loads((p/'receipt.json').read_text());out=(p/'stdout.log').read_text();m=re.search(r'BOX_NATIVE_OK pairs=(\d+) raw_cells=(\d+) materialized_cells=(\d+) size=(\d+) align=(\d+)',out);assert rec['exit_status']==0 and m,out[-4000:]
rest=json.loads((E/'batch2f-box-native-001/restored.json').read_text());assert rest['restored']
j=dict(passed=True,classification='Optimized compile/static Rust layout assertion and finite native source/copy allocation/drop/value comparison; no proof generation/elimination and no native OOM injection',constructor_pairs=int(m[1]),raw_cells=int(m[2]),materialized_cells=int(m[3]),layout=dict(size=int(m[4]),alignment=int(m[5])),allocations_and_drops='Exactly one allocation and one deallocation of the identical layout for each original/copy constructor pair; every allocated byte reclaimed by Drop in these tests',actual_copy_factory='crate::prover::retain_weights_box',receipt='candidate/batch2f-box-native-001/receipt/receipt.json',source_revision=rec['source_revision'],wall_seconds=rec['wall_seconds'],peak_rss_kib=rec['peak_rss_kib'],swaps=rec['swaps'],native_oom_observed=False,modeled_failures='40838 and universal Lean Box request context',source_restored=rest)
(E/'NATIVE-BOX-FIDELITY.json').write_text(json.dumps(j,indent=2)+'\n');print(j)
