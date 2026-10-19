#!/usr/bin/env python3
"""Interpret exact emitted dots declarations under explicit shared parameters."""
from pathlib import Path
import argparse,hashlib,json
ap=argparse.ArgumentParser();ap.add_argument('--check',action='store_true');args=ap.parse_args()
here=Path(__file__).resolve().parent;area=here.parents[1]
raw=(here/'cu-dots-generated/Funs.lean').read_bytes()
assert hashlib.sha256(raw).hexdigest()=='8ab0c6587f960702f4619ebc450c988e2c9c1aac3aa9dd4c2a90a6ef393adb5c'
types=(here/'cu-dots-generated/Types.lean').read_bytes()
assert hashlib.sha256(types).hexdigest()=='545cb4c9320681ef1f60b828bca4aa5af076fd12218944253c589b8018e6fede'
marker=b'namespace AspisR1CuDots\n'
assert raw.count(marker)==1
output=raw.replace(marker,marker+b'\nvariable [Arithmetic]\n',1)
assert output.replace(b'\nvariable [Arithmetic]\n',b'',1)==raw
sha=lambda b:hashlib.sha256(b).hexdigest()
outputs={area/'lean/AspisR1CuDots/Types.lean':types,
         area/'lean/AspisR1CuDots/Funs.lean':output}
pins=dict(input_sha256=sha(raw),output_sha256=sha(output),
    layout_changes=['One namespace variable [Arithmetic] generalizes shared callees; every emitted declaration body remains byte-identical.'],
    scope='Universal arithmetic interpretation and concrete state-threading array builder; generated axiom template is not imported. Actual loop/caller equivalence and standard-library admission remain required.')
outputs[here/'cu-dots-emission.json']=(json.dumps(pins,indent=2)+'\n').encode()
for path,data in outputs.items():
    if args.check:assert path.read_bytes()==data,str(path)
    else:path.parent.mkdir(parents=True,exist_ok=True);path.write_bytes(data)
print(json.dumps(dict(check=args.check,output_sha256=sha(output))))
