from pathlib import Path
import hashlib,re,json
r=Path(__file__).resolve().parent
b=(r/'candidate-current.rs').read_bytes()
expected='5164975df10f79e9810f9321b8130a9865eb9bb9b6b9de7011f4359ece98c794'
assert hashlib.sha256(b).hexdigest()==expected
m=re.search(rb'fn query_values\s*\(',b);assert m
op=b.find(b'{',m.start())
needle=b'let dots = crate::fast_dots::four_dots(q, g);'
pos=b.find(needle,op);assert pos>=0
prefix=b[op+1:pos+len(needle)]
assert prefix==b'\n    let i = a.next;\n    let u = p.queries[i] as usize;\n    let q = opening(proof, i);\n    '+needle
print('PASS current pinned query_values performs opening(proof,i), then four_dots(q,g) in source order')
