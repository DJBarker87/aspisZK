from pathlib import Path
import subprocess,json,lzma,sys
sys.dont_write_bytecode=True
E=Path(__file__).resolve().parent
for i,n in enumerate(['registry_array_wrong','entry_array','entry_array_wrong','registry_word','registry_word_wrong','entry_word','entry_word_wrong'],50):
 r=subprocess.run([sys.executable,str(E/'NHY_run.py'),f'NHY_K{i:03}','kani','statement:pool_v1::verifier_registry::NHY_registry::'+n],capture_output=True,text=True)
 print(r.stdout[-4000:],flush=True)
 if not (E/f'NHY_K{i:03}'/'receipt.json').exists():sys.exit(1)
 code=json.loads((E/f'NHY_K{i:03}'/'receipt.json').read_text())['exit_status']
 s=lzma.decompress((E/f'NHY_K{i:03}'/'stdout.log.xz').read_bytes()).decode()
 if code!=(1 if n.endswith('_wrong') else 0) or 'timed out' in s:sys.exit(1)
