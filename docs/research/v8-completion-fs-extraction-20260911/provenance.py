#!/usr/bin/env python3
"""Inventory supplied zip bytes without executing/extracting archive entries."""
import hashlib,json,sys,zipfile
from pathlib import Path
here=Path(__file__).resolve().parent
archive=Path(sys.argv[1])
result={'archive_sha256':hashlib.sha256(archive.read_bytes()).hexdigest(),'members':{}}
with zipfile.ZipFile(archive) as z:
    for name in z.namelist():
        if name.endswith('/'):continue
        relative=Path(*Path(name).parts[1:])
        local=here/'supplied'/relative
        original=hashlib.sha256(z.read(name)).hexdigest()
        current=hashlib.sha256(local.read_bytes()).hexdigest() if local.is_file() else None
        result['members'][str(relative)]={'original_sha256':original,'working_sha256':current,
            'status':'IDENTICAL' if current==original else ('MODIFIED' if current else 'NOT_COPIED')}
output=here.parents[2]/'results'/here.name/'archive-provenance.json'
output.write_text(json.dumps(result,indent=2)+'\n')
print(len(result['members']),'archive files;',output)
