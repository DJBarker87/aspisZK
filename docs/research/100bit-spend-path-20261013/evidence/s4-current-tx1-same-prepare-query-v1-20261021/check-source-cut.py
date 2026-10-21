import pathlib,re,hashlib,sys
base=pathlib.Path(__file__).parent/'sources'
raw=(base/'AspisR1CurrentCaller/Funs.lean').read_text()
cut=(base/'Tx1OpsCut.lean').read_text()
def extract(s, start, end):
    a=s.index(start); b=s.index(end,a); return s[a:b]
r=extract(raw,'def verifier.candidate.tx1','\nend AspisR1CurrentCaller')
c=extract(cut,'def tx1 {H : Type}','\nend AspisR1CallerV4Tx1OpsCut')
after=extract(cut,'def afterPrepared {H : Type}','\n\ndef tx1 {H : Type}')
r=r[r.index(':= do'):]
c=c[c.index(':= do'):]
after=after[after.index(':= do')+len(':= do'):]
# Expand the single exact helper invocation used by the cut back to its checked source body.
actual_call='afterPrepared ops inst val g1 proof public_bytes k hash obs'
for old,new in [('prepared','val'),('scratch','g1')]:
    after=re.sub(r'\b'+old+r'\b',new,after)
if c.count(actual_call)!=1:
    raise SystemExit(f'FAIL: expected one afterPrepared call, found {c.count(actual_call)}')
c=c.replace(actual_call,after)
repls=[
('verifier.candidate.parse_shape','ops.parseShape'),
('verifier.candidate.canonical_scan','ops.canonicalScan'),
('verifier.candidate.prepare aspis_coredigestDigest32Inst','ops.prepare inst'),
('verifier.Accumulator.new','ops.accumulatorNew'),
('verifier.candidate.batch_merkle aspis_coredigestDigest32Inst','ops.batchMerkle inst'),
('verifier.QueryGeometry.for_range','ops.makeGeometry'),
('verifier.BatchedWeights.new','ops.weightsNew'),
('verifier.candidate.query_loop','ops.queryLoop'),
('verifier.BatchedWeights.finish','ops.weightsFinish'),
('verifier.checkpoint aspis_coredigestDigest32Inst','ops.checkpoint inst'),
('verifier.mark','ops.mark'),
('compact.SPLIT','ops.split'),
('compact.OFF_FOLDED_ROOT','ops.offFoldedRoot'),
('compact.OFF_ROUND1','ops.offRound1'),
('aspis_core.field.wide_exact.WideExact.ZERO','ops.zero'),
('core.result.Result.Err','.Err'),('core.result.Result.Ok','.Ok')]
for a,b in repls:r=r.replace(a,b)
def norm(s): return re.sub(r'\s+',' ',s).strip()
if norm(r)!=norm(c):
    import difflib
    print('FAIL: normalized bodies differ')
    print('\n'.join(difflib.unified_diff(norm(r).split(),norm(c).split(),fromfile='generated-substituted',tofile='Ops-cut-expanded',lineterm='')))
    sys.exit(1)
print('PASS: full tx1 body matches generated caller-v4 after 15 explicit operation-slot substitutions and exact afterPrepared expansion')
for p in [base/'AspisR1CurrentCaller/Funs.lean',base/'Tx1OpsCut.lean']:
    print(p.name+'_sha256',hashlib.sha256(p.read_bytes()).hexdigest())
