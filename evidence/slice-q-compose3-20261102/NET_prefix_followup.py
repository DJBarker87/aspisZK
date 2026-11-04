from pathlib import Path
import json,subprocess,sys
E=Path(__file__).resolve().parent
assert not (E/'NET_ACTIVE.json').exists()
for n,tail in [(83,'KMX_ptr_correct'),(84,'KMX_ptr_wrong')]:
 a=f'NET_K{n:03}'
 subprocess.run([sys.executable,str(E/'NET_kani.py'),a,'verifier::NET_prefix::KMX_checks::'+tail])
 r=json.loads((E/a/'receipt.json').read_text());assert r['exit_status']==int(n==84)
for n,m in enumerate(['NEG_PrefixFull.Types','NEG_PrefixFull.FunsExternal','NEG_PrefixFull.Funs','NEG_PrefixAssociation','NBS_GeometryDomains','NET_PrefixClosure'],19):
 subprocess.run([sys.executable,str(E/'NET_run.py'),f'NET_L{n:03}',m],check=True)
