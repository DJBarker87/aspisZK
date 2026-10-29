"""Pin ordered source stages; never claim a complete bridge from a name/hash."""
from pathlib import Path
import json,re,hashlib
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-owni-20261029'
sources=json.loads((E/'deployed-sources.json').read_text())['rows']
sha=lambda b:hashlib.sha256(b).hexdigest()
def span(path,a,b):
 r=next(r for r in sources if r['path'].endswith(path));s='\n'.join(r['text'].splitlines()[a-1:b])+'\n';return dict(path=r['path'],file_sha256=r['sha256'],first_line=a,last_line=b,text=s,sha256=sha(s.encode()))
rows=[]
# Twenty actual ordered scalar/tower bodies, all immutable by-value arithmetic.
for p in sorted((R/'docs/research/v8-r0-zk-20261009/lean/R1Z').glob('PV_B2_W_*.lean')):
 if int(p.name.split('_')[3])>19:continue
 t=p.read_text();m=re.search(r"Source: '([^']+)', lines (\d+):",t);assert m,p
 name=re.search(r'def (aspis_core\.field\.[\w.]+)',t)[1]
 src=next(r for r in sources if r['path']==m[1]);lines=src['text'].splitlines();start=int(m[2]);depth=0;beg=False;end=start
 # constant P has no body; regular definitions use matched braces.
 for i in range(start-1,len(lines)):
  z=lines[i].split('//')[0];depth+=z.count('{')-z.count('}');beg=beg or '{' in z;end=i+1
  if (beg and depth==0) or (not beg and ';' in z):break
 rust='\n'.join(lines[start-1:end]);assert not any(x in rust for x in ['Vec::','alloc(','errno','thread_local','static mut','unsafe'])
 assert not re.search(r'let\s*\([^\n]*,\s*_\)',t),p
 rows.append(dict(name=name,rust=span(m[1],start,end),lean_path=str(p.relative_to(R)),lean_sha256=sha(p.read_bytes()),lean_result_calls=re.findall(r'←\s+(aspis_core\.[\w.]+)',t),association='immutable scalar/record expressions; ordered let bindings; u32/u64 wrapping profile and compiler primitives retained at V370',mutable_restore_check='no mutable borrow or discarded restoration; pure by-value cone'))
# Retain exact relevant source excerpts; these are coverage obligations, not proof.
root=span('crates/aspis-statement/src/constraints_v4.rs',782,796)
builder=span('crates/aspis-statement/src/constraints_v4.rs',601,632)
assert 'Vec::with_capacity(1usize << prefix_len)' in builder['text']
assert 'weights.push((row, weight))' in builder['text']
assert 'sum.add(weight.mul(column[row]))' in root['text']
# Static resource channels: the data-bearing fold has no allocating/destructing
# callee; QM31 tower uses no pointer-derived arithmetic or external state.
resource=dict(allocation='one with_capacity, 24*2^prefix bytes/alignment8; prefix from point only',growth='exact range cardinality equals capacity; no grow branch once builder cardinality/typed stores are composed',drop='POD tuple slice drop then backing RawVec deallocation; no data destructor',failure='null allocation invokes default allocation error handler; rdea-1, not a success precondition',channels='no pointer integer values, address comparisons/hashes, errno or allocator-written state read feeds caller; native address arithmetic only ptr.add/offset and loop end; sizes/offsets from public point/length',limitations='source excerpts and scalar association do not prove concrete numeric-to-byte Vec instance or sparse/dense/public consumer composition')
(E/'source-binding.json').write_text(json.dumps(dict(classification='partial structural source binding under own-1; not whole-row restoration',raw_methods=rows,root=root,builder=builder,resource=resource,compiler_boundary='V370/D381/D386 retained; existing Aeneas/Rust semantic agreement is reclassification within existing tool trust'),indent=2)+'\n')
print(len(rows),'raw methods; root and builder pinned')
