from pathlib import Path
import re, hashlib
root = Path(__file__).resolve().parent
raw=(root/'sources/FourDotsFixedV6-Funs.lean').read_text()
import hashlib
assert hashlib.sha256(raw.encode()).hexdigest() == '38276aed2316117b0b17d492f2e1e9894de1cce0e8c2db306ddf34bae011c760'
start=raw.index('namespace AspisR1FastDotsCurrent')
end=raw.index('\nend AspisR1FastDotsCurrent',start)
body=raw[start:end].split('\n',1)[1]
# Split into generated declaration chunks, preserving each emitted body text.
starts=list(re.finditer(r'(?m)^def (fast_dots\.[A-Za-z0-9_.]+)\n',body))
assert len(starts)==6, len(starts)
chunks=[]
for i,m in enumerate(starts):
    chunkStart=m.start()
    chunkEnd=starts[i+1].start() if i+1<len(starts) else len(body)
    chunk=body[chunkStart:chunkEnd]
    # The emitted signature gets an explicit operation-record argument.
    name=m.group(1)
    chunk=chunk.replace('def '+name+'\n','def '+name+'\n  (ops : FourDotsOps)\n',1)
    sig,sep,impl=chunk.partition('  := do\n')
    assert sep, name
    # Reuse the accepted source-pinned S4 operation record instead of generated stubs.
    for op,field in [
      ('aspis_core.field.M31.from_le_bytes','m31FromBytes'),
      ('aspis_core.field.M31.reduce_u64','m31ReduceU64'),
      ('aspis_core.field.QM31.from_le_bytes','qm31FromBytes'),
      ('aspis_core.field.wide_exact.WideExact.to_limbs','wideToLimbs'),
      ('aspis_core.field.wide_exact.WideExact.from_limbs','wideFromLimbs'),
      ('aspis_core.field.wide_exact.WideExact.add','wideAdd'),
      ('fast_pairing.EbyKDot.new','ebyKNew'),
      ('fast_pairing.EbyKDot.push','ebyKPush'),
      ('fast_pairing.EbyKDot.finish','ebyKFinish')]:
        impl=impl.replace(op,'ops.'+field)
    # Thread the exact same explicit source-operation record through generated local calls.
    for n in sorted((x.group(1) for x in starts),key=len,reverse=True):
        impl=re.sub(re.escape(n)+r'(?=\s)',n+' ops',impl)
    chunks.append(sig+sep+impl)
header='''import Aeneas
import AspisR1FastDotsCurrent.FunsOpsV4
open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false
noncomputable section
namespace AspisR1FastDotsCurrent
'''
out=header+'\n'.join(chunks)+'\nend AspisR1FastDotsCurrent\n'
expected=(root/'sources/FunsOpsFixedV6.lean').read_text()
assert out == expected, 'adapted six-definition source differs from generated output'
assert hashlib.sha256(out.encode()).hexdigest() == 'bf743f23348997dfc24c538658fd6af89ce72eac66ef6f45158e1e5cfb21214b'
assert hashlib.sha256((root/'sources/FourDotsFixedCallSuccessV1.lean').read_bytes()).hexdigest() == 'a1eeca53e2a07f5515db4fd0c2036e60f2c595946890518b82602431acf64990'
assert len(starts) == 6
assert 'FunsExternal_Template' not in out and 'TypesExternal_Template' not in out
assert 'set_option maxHeartbeats' not in out and 'set_option maxRecDepth' not in out
print('PASS: exact adapted source,', len(out), 'bytes; defs',len(starts))
for n in starts: print(n.group(1))
