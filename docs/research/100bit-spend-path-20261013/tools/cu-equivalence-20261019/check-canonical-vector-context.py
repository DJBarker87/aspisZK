from pathlib import Path
import hashlib,json,subprocess,argparse
p=argparse.ArgumentParser();p.add_argument('--check',action='store_true');args=p.parse_args();tool=Path(__file__).resolve().parent
# Re-execute the immutable extraction recipe only through its source preparation.
scope={'__file__':str(tool/'extract-canonical-vector-callers.py')}
code=(tool/'extract-canonical-vector-callers.py').read_text().split("e_start=v.index")[0]
exec(code,scope)
globals().update(scope)
# Pin the complete enclosing contexts and check the inverse source factoring.
# These are source certificates, not replacement production implementations.
claim_start=v.index(b'fn prepared_claim');claim_end=block(v,claim_start)
claim_full=v[claim_start:claim_end]
claim_piece=chunk+b'\n            parts[point+1]=dot.finish();'
assert claim_full.count(claim_piece)==1
claim_context=claim_full.replace(claim_piece,b'parts[point+1]=SOURCE_CLAIM_DOT(point,g)?;')
assert claim_context.replace(b'parts[point+1]=SOURCE_CLAIM_DOT(point,g)?;',claim_piece)==claim_full
assert b'dot' not in scalar and not __import__('re').search(rb'\bg\b',scalar)
fast_start=f.index(b'pub fn four_dots');fast_end=block(f,fast_start)
fast_full=f[fast_start:fast_end];tail_piece=tail+b'\n        value.add(tail.finish())'
assert fast_full.count(tail_piece)==1
fast_context=fast_full.replace(tail_piece,b'value.add(SOURCE_TAIL(q,g,slot))')
assert fast_context.replace(b'value.add(SOURCE_TAIL(q,g,slot))',tail_piece)==fast_full
for name,full,context,piece,source in [('claim-context',claim_full,claim_context,claim_piece,v),('tail-context',fast_full,fast_context,tail_piece,f)]:
 assert full in at(vp if name=='claim-context' else fp,rev+'^')
 pins[name]=dict(full_sha256=sha(full),context_sha256=sha(context),factor_sha256=sha(piece),inverse_checked=True,parent_candidate_full_body_identical=True,scope='Universal checked context substitution consumes exact source loop equality; scalar common expression is independent of changed dot state.')
 out[name+'.source.rs']=full;out[name+'.factored.rs']=context

frozen='39c2971dd16c95858a4cfd2c9ae35da052eacfa9'
assert claim_full in at(vp,frozen)
assert tail_piece in at(fp,frozen)
for name in ['claim-context','tail-context']:
 pins[name]['frozen_revision']=frozen
 pins[name]['frozen_changed_source_region_identical']=True
report={k:pins[k] for k in ['claim-context','tail-context']}
for name in ['claim-context.source.rs','claim-context.factored.rs','tail-context.source.rs','tail-context.factored.rs']:
 target=here/'canonical-vector-context-audit'/name
 if args.check: assert target.read_bytes()==out[name]
 else: target.parent.mkdir(parents=True,exist_ok=True);target.write_bytes(out[name])
target=here/'canonical-vector-context-audit/source-pins.json';data=(json.dumps(report,indent=2)+'\n').encode()
if args.check:assert target.read_bytes()==data
else:target.write_bytes(data)
print(json.dumps(dict(check=args.check,inverse_contexts=2)))
