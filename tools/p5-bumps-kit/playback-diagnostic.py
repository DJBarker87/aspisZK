#!/usr/bin/env python3
import json,re,sys
from pathlib import Path
h=Path(__file__).resolve().parent
source=Path(sys.argv[1]);log=Path(sys.argv[2])
s=source.read_text();txt=log.read_text();i=txt.index('#[test]\nfn kani_concrete_playback_prepared_shard_decode_');j=txt.index('\n```',i);test=txt[i:j]
start=s.index('mod prepared_shard_decode {');end=s.index('\n}\n}',start)+len('\n}')
s=s[:end]+'\n'+test+'\n'+s[end:]
source.write_text(s)
pins=json.loads((source.parent/'source-pins.json').read_text());pins['scope']='Diagnostic: exact Kani-emitted concrete playback inserted into the original shard harness; not a proof result';(source.parent/'source-pins.json').write_text(json.dumps(pins,indent=2)+'\n')
print(re.search(r'fn (kani_concrete\w+)',test)[1])
