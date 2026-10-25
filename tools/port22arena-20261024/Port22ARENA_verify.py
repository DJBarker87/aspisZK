import hashlib,json,pathlib,sys
pins=json.load(sys.stdin)
for p,h in pins.items(): assert hashlib.sha256(pathlib.Path(p).read_bytes()).hexdigest()==h,p
print(json.dumps(dict(verified_tool_sysroot_hashes=len(pins))))
