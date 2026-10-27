"""One named native coordinate contract through the unchanged receipt helper.
Admission and cgroup scope are supplied by the caller. No scope is launched here.
"""
from pathlib import Path
import hashlib,json,subprocess,sys
cases=['row_index_native_reference','coordinate_m31_all','coordinate_qm31_all','coordinate_wide_all','coordinate_m31_s1','coordinate_m31_d','coordinate_qm31_s1','coordinate_qm31_d','coordinate_wide_s1','coordinate_wide_d']
number=int(sys.argv[1]);assert 1<=number<=len(cases)
case=cases[number-1];label=f'pdict262-kani-{number:03d}'+(sys.argv[2] if len(sys.argv)>2 else '')
proof=Path('tools/prover-dict-20261026/proof-coordinate262')
inputs=[*proof.iterdir(),Path('tools/prover-dict-20261026/proof-world244/row.rs'),Path(__file__)]
pins={str(p):dict(sha256=hashlib.sha256(p.read_bytes()).hexdigest(),bytes=p.stat().st_size) for p in inputs if p.is_file()}
cmd=['timeout','120','cargo','kani','--manifest-path',str(proof/'Cargo.toml'),'--lib','--harness',case,'--exact','--solver','kissat','-j','4','--output-format','terse']
print(label,case,flush=True)
ret=subprocess.run([sys.executable,'tools/prover-rw-20261023/host-run.py',label,*cmd]).returncode
out=Path('receipts')/label
if (out/'receipt.json').exists():
 (out/'input-supplement.json').write_text(json.dumps(dict(source_revision='41e05299e9 plus exact proof-only hashes below',proof_inputs=pins,command=cmd,exit_status=ret,statement='One native output array vs scalar expected coordinate; arbitrary selected inputs, no stubs, all bounds/overflow/unwinding guards retained.',expected_work='Optimized opt-level3 compilation, then the named array/bitvector contract; no arithmetic elimination.',raw_revision_qualification='The historical source-revision.txt in the reused host workspace is not relabelled. This supplement pins new proof inputs; the source binding checks the unchanged production modules separately.'),indent=2)+'\n')
sys.exit(ret)
