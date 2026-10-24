"""Read-only post-extraction object inventory; never a fresh ELF identity gate."""
from pathlib import Path
import hashlib,json,sys,time
D=Path(__file__).resolve().parent;start=time.monotonic()
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
files=[dict(path=str(p.relative_to(D)),sha256=sha(p),size=p.stat().st_size)
       for p in sorted((D/'target').rglob('*')) if p.is_file()]
out=dict(schema='ProverRwFactoryState-post-extraction-objects-v1',command=sys.argv,
    source_revision=(D/'revision.txt').read_text().strip(),script_sha256=sha(Path(__file__)),
    files=files,wall_seconds=time.monotonic()-start,actual_compiler_invocations=0,
    claim='post054 prospective selected-crate objects only; not deployed ELF identities',
    preflight_objects='New factory-state target directory absent before054; no prior compiled crate/cache objects reused. Sysroot/dependency rlibs included in preflight/go hashes.',
    print_axioms='N/A: read-only object hash inventory')
Path(sys.argv[1]).write_text(json.dumps(out,indent=2)+'\n')
print('PASS post-extraction object inventory',len(files),'files; no object bytes copied')
