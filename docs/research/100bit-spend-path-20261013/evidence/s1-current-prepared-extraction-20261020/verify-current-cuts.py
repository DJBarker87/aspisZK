#!/usr/bin/env python3
from pathlib import Path
import argparse, hashlib, json, subprocess
ap=argparse.ArgumentParser();ap.add_argument("kit",type=Path);a=ap.parse_args()
root=Path(__file__).resolve().parents[5];pins=json.loads((a.kit/"source-pins.json").read_text());sha=lambda b:hashlib.sha256(b).hexdigest()
for cut in pins["cuts"]:
    raw=subprocess.check_output(["git","-C",str(root),"show",pins["revision"]+":"+cut["path"]])
    fragment=(a.kit/"fragments"/(cut["name"]+".rs")).read_bytes()
    assert sha(raw)==cut["source_file_sha256"]
    assert raw[cut["start_byte"]:cut["end_byte_exclusive"]]==fragment
    assert sha(fragment)==cut["sha256"]
    assert (a.kit/"lib.rs").read_bytes().count(fragment)==1,cut["name"]
for name,h in pins["kit_files"].items():
    assert sha((a.kit/name).read_bytes())==h,name
assert len(pins["cuts"])==20
new=(a.kit/"fragments/prepared_new.rs").read_bytes()
assert b"g:&mut [E;29]" in new and new.count(b"*g=powers::<29>(gamma);")==1
print("PASS: 20 exact current source cuts; gamma scratch API/body preserved; kit file hashes exact")
