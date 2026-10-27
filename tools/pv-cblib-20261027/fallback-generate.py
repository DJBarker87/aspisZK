"""Source-preserving fallback scaffolding generator; no accelerated-backend claim.

Every generated stage refers to an extracted helper theorem rather than
normalizing concrete SHA states or expanding a 64-round recurrence.
"""
from pathlib import Path
import hashlib,json,re,sys
root=Path(__file__).resolve().parents[2];out=root/'evidence/pv-cblib-20261027';b=root/'docs/research/v8-r0-zk-20261009/lean/R1Z'
source=out/'source/sha2-0.10.9__src__consts.rs'
s=source.read_text();vals=re.findall(r'0x[0-9a-f]+',s[s.index('pub const K32:'):s.index('pub const K32X4:')]);assert len(vals)==64
# Constants have no recurrence or expensive kernel graph. Grouped per four rounds.
head='''import R1Z.PV_CBL_FallbackArray4
open Aeneas Aeneas.Std Result
namespace R1Z.PV_CBL_FallbackConstants
set_option autoImplicit false
'''
body='def words : List U32 := [\n'+',\n'.join('  '+', '.join(str(int(v,16))+'#u32' for v in vals[i:i+4]) for i in range(0,64,4))+'\n]\n'
body+='theorem words_length : words.length=64 := rfl\n#print axioms words\n#print axioms words_length\n'
text=head+body+'end R1Z.PV_CBL_FallbackConstants\n'
p=b/'PV_CBL_FallbackConstants.lean'
if '--check' in sys.argv:assert p.read_text()==text
else:p.write_text(text)
(out/'fallback-constant-generation.json').write_text(json.dumps(dict(source_sha256=hashlib.sha256(source.read_bytes()).hexdigest(),output_sha256=hashlib.sha256(text.encode()).hexdigest(),words=64,kind='pinned constant list; not a compression theorem'),indent=2)+'\n')
