"""One bounded candidate007 invocation per case; negative output is never used."""
from pathlib import Path
import hashlib,json,subprocess,sys
D=Path(__file__).resolve().parent
H=D.parents[2].parent
binary=H/'rng-extractor/candidate-007/main.exe'
build=H/'rng-extractor/prover-rw-rng-extractor-build-007/receipt.json'
expected=json.loads(build.read_text())['versioned_binary']
assert hashlib.sha256(binary.read_bytes()).hexdigest()==expected['sha256']
kind=sys.argv[1]
assert kind in ['minimal','selected64']
inp=D/'ProverRwNativeEntropyDropV4.llbc' if kind=='minimal' else D.parent/'rng-extractor/ProverRwRngExtractorselected64.llbc'
dest=D/('rejected-'+kind)
assert not dest.exists()
cmd=[str(binary),'-sequential','-no-progress-bar','-abort-on-error','-backend','lean',
    '-namespace','ProverRwNativeEntropyRejected','-dest',str(dest),'-split-files','-emit-json',str(inp)]
pin=lambda p:dict(sha256=hashlib.sha256(p.read_bytes()).hexdigest(),bytes=p.stat().st_size)
(D/(kind+'-guard-pins.json')).write_text(json.dumps(dict(command=cmd,binary=pin(binary),
    build_receipt=pin(build),input=pin(inp),print_axioms='N/A: negative preflight'),indent=2)+'\n')
result=subprocess.run(cmd)
(D/(kind+'-guard-status.json')).write_text(json.dumps(dict(exit_status=result.returncode,
    output_directory_exists=dest.exists(),accepted_artifact=False),indent=2)+'\n')
raise SystemExit(result.returncode)
