from pathlib import Path
import json,re,hashlib
E=Path(__file__).resolve().parent;S=E.parent.parent/'programs/aspis-pool/src/empty_roots.rs';s=S.read_text();start=s.index('pub const POOL_V1_EMPTY_ROOTS:');end=s.index('\n];',start);part=s[start:end]
assert '[M31::ZERO; DIGEST_ELEMS]' in part
words=[int(v.replace('_',''),0) for v in re.findall(r'M31\((0x[0-9a-fA-F_]+|[0-9_]+)\)',part)];assert len(words)==20*8
pair=s[s.index('pub const POOL_V1_PAIR_EMPTY_ROOTS:'):];refs=[int(n) for n in re.findall(r'POOL_V1_EMPTY_ROOTS\[(\d+)\]',pair.split('\n];')[0])];assert refs==list(range(1,21))
rows=[words[8*i:8*(i+1)] for i in range(20)]
body='import PCD_LaneRef.Types\nset_option autoImplicit false\nnamespace PCD_EmptyRoots\nopen Aeneas.Std\ndef roots : Array (Array U32 8#usize) 20#usize :=\n  ⟨[\n'+',\n'.join('    ⟨['+','.join(str(w)+'#u32' for w in r)+'],rfl⟩' for r in rows)+'\n  ],rfl⟩\nend PCD_EmptyRoots\n'
(E/'PCD_EmptyRoots.lean').write_text(body)
(E/'PCD_EMPTY_ROOTS_PINS.json').write_text(json.dumps({'source':'programs/aspis-pool/src/empty_roots.rs','source_sha256':hashlib.sha256(s.encode()).hexdigest(),'source_relation':'PAIR_EMPTY_ROOTS[level] = EMPTY_ROOTS[level+1] for 0<=level<20; pair-specific top root at 20 is not read by POOL:320','word_rows':rows,'lean_sha256':hashlib.sha256(body.encode()).hexdigest(),'status':'source literal transcription; no recurrence evaluated'},indent=1)+'\n')
print('PCD twenty empty-root literals emitted with exact shifted-table source association; no arithmetic replay.')
