"""Read the retained K009 GOTO, or diagnose one exact assertion. No native credit."""
from pathlib import Path
import hashlib,json,subprocess,sys
B=Path(__file__).resolve().parent
G=B/'NIH_target/kani/x86_64-unknown-linux-gnu/debug/deps/aspis_statement-7bbb061b86d42267__RNvNtNtNtCs37UJtixU7ll_15aspis_statement7pool_v129pair_forest_semantic_terminal10NHU_native19NHU_transition_step.out'
cb=Path('/home/dombarker/.kani/kani-0.67.0/bin/cbmc')
args=['--show-properties'] if sys.argv[1]=='show' else ['--unwind','200','--trace','--stop-on-fail','--property',sys.argv[1]]
(B/(sys.argv[2]+'-goto-pin.json')).write_text(json.dumps(dict(path=str(G),sha256=hashlib.sha256(G.read_bytes()).hexdigest(),bytes=G.stat().st_size,cbmc_sha256=hashlib.sha256(cb.read_bytes()).hexdigest(),command=[str(cb),str(G),*args],credit='DIAGNOSTIC ONLY'),indent=2)+'\n')
sys.exit(subprocess.run([str(cb),str(G),*args]).returncode)
