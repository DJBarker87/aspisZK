import subprocess,sys
from pathlib import Path
p=Path(__file__).parent
for m in ['RWireConstructedWords', 'RWireRawCutLaterTableLiteralWords', 'RWireLiteralTableChoiceWords', 'RWireRawLiteralRecordedDecoder', 'RWireRawLiteralCompiledDecoder', 'RWireRawCompiledTranscript', 'RWireRawCompiledDecoderCompletion', 'RWireRawFullPublicRun', 'RWireRawAdaptiveCompiledCompletion']:
 import json,hashlib
 data=json.loads((p/"manifest.json").read_text())
 src=p.parents[1]/"lean"/(m+".lean")
 if any(a["module"]==m and a["final_current"] and a["source_sha256"]==hashlib.sha256(src.read_bytes()).hexdigest() for a in data["attempts"]): continue
 r=subprocess.run([sys.executable,str(p/"compile.py"),m])
 if r.returncode: sys.exit(r.returncode)
