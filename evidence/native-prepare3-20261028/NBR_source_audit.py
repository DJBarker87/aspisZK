"""Source-position association for semantic row fission; no semantic proof credit."""
from pathlib import Path
import subprocess,hashlib,json,re
E=Path(__file__).resolve().parent
rev='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387'
p='crates/aspis-r1-cost-probe/src/compact.rs'
s=subprocess.check_output(['git','show',rev+':'+p],text=True)
h=Path('/private/tmp/NBR_semantic_row.rs').read_text()
a=s.index('        let size = row_shape(row).ok_or(CodecError::Length)?.1;',s.index('pub fn expand_semantic'))
b=s.index('\n    }\n    if src != compact.len()',a)
original=s[a:b]
a=h.index(' let size=crate::r1_wire::row_shape(row).ok_or(CodecError::Length)?.1;')
b=h.index('Ok((src,dst))',a)
fission=h[a:b]
normalize=lambda x:re.sub(r'\s+','',x).replace('crate::r1_wire::row_shape','row_shape').replace('compact::expand_values','expand_values').replace('compact_row(row)','row>=14')
assert normalize(original)==normalize(fission),(normalize(original),normalize(fission))
assert 'fn compact_row(row: u8) -> bool {\n    row >= 14\n}' in s
x=dict(revision=rev,source=p,source_sha256=hashlib.sha256(s.encode()).hexdigest(),fission_sha256=hashlib.sha256(h.encode()).hexdigest(),tokens_match=True,substitutions=['qualify row_shape/expand_values','compact_row(row) = row >= 14 (verbatim pure source body)','return current src,dst in place of next loop iteration'],qualification='Static source association only; native step gate, byte/frame induction and K-1 obligations remain separate')
(E/'NBR_SEMANTIC_SOURCE.json').write_text(json.dumps(x,indent=2)+'\n')
print(json.dumps(x))
