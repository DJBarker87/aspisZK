#!/usr/bin/env python3
from pathlib import Path
import re, sys
src = Path(sys.argv[1]).read_text()
out = Path(sys.argv[2])
if src.count('namespace V7CallerCurrentReleaseR24') != 1 or src.count('end V7CallerCurrentReleaseR24') != 1:
    raise SystemExit('unexpected R24 module boundary')
old = 'import Aeneas\n'
new = 'import Aeneas.Std\nimport Aeneas.Data.Discriminant\nimport Aeneas.Tactic.RustAttributes\n'
if src.count(old) != 1: raise SystemExit('Aeneas import count')
src = src.replace(old,new,1)
for a,b,n in [
 ('field.M31.impl.','field.M31.',136),
 ('field.CM31.impl.','field.CM31.',0),
 ('field.QM31.impl.','field.QM31.',0),
 ('core.num.U16.impl.','core.num.U16.',5),
 ('core.num.U32.impl.','core.num.U32.',3),
 ('core.num.U64.impl.','core.num.U64.',0),
 ('core.num.Usize.impl.','core.num.Usize.',0),
 ('core.option.Option.impl.','core.option.Option.',4),
 ('core.option.OptionShared0T.impl.','core.option.OptionShared0T.',0),
 ('core.result.Result.impl.','core.result.Result.',24),
 ('core.slice.Slice.impl.','core.slice.Slice.',4),
 ('alloc.vec.Vec.impl.','alloc.vec.Vec.',6),
]:
    got=src.count(a)
    if n and got != n: raise SystemExit(f'{a} expected {n}, got {got}')
    src=src.replace(a,b)
old='core.array.Array.impl.'
if src.count(old)!=1: raise SystemExit(f'array map method count: {src.count(old)}')
src=src.replace(old,'core.array.Array.')
pat=r'(?<![A-Za-z0-9_\.])transcript\.'
got=len(re.findall(pat,src))
if got < 50: raise SystemExit(f'transcript refs unexpectedly sparse: {got}')
src=re.sub(pat, '_root_.V7CallerCurrentReleaseR24.transcript.', src)
for old,new,count in [
 ('next := core.slice.iter.IteratorIterMut.next\n','next := core.slice.iter.IteratorIterMut.next_without_writeback\n',1),
 ('let im1 := enumerate_back back','let im1 := enumerate_back (back iter)',1),
]:
 if src.count(old)!=count: raise SystemExit(f'iterator shape {old!r}: {src.count(old)}')
 src=src.replace(old,new)
old='''core.iter.adapters.enumerate.IteratorEnumerate.next
      (core.slice.iter.IterMut.Insts.CoreIterTraitsIteratorIteratorMutAT
      field.QM31) iter'''

if src.count(old)!=1: raise SystemExit(f'QM31 enumerate next count: {src.count(old)}')
src=src.replace(old,'core.iter.adapters.enumerate.IteratorEnumerateMut.next iter')
old='''core.iter.traits.iterator.Iterator.enumerate.trait_default
      (core.slice.iter.IterMut.Insts.CoreIterTraitsIteratorIteratorMutAT
      field.QM31) im'''
if src.count(old)!=1: raise SystemExit(f'QM31 enumerate constructor count: {src.count(old)}')
src=src.replace(old,'core.iter.adapters.enumerate.IteratorEnumerateMut.enumerate im')
old='''core.iter.adapters.enumerate.IteratorEnumerate.next
      (core.slice.iter.IterMut.Insts.CoreIterTraitsIteratorIteratorMutAT (Array
      field.QM31 4#usize)) iter'''
if src.count(old) not in (0,1): raise SystemExit(f'array enumerate next count: {src.count(old)}')
src=src.replace(old,'core.iter.adapters.enumerate.IteratorEnumerateMut.next iter')
old='''core.iter.traits.iterator.Iterator.enumerate.trait_default
      (core.slice.iter.IterMut.Insts.CoreIterTraitsIteratorIteratorMutAT (Array
      field.QM31 4#usize)) im'''
if src.count(old) not in (0,1): raise SystemExit(f'array enumerate constructor count: {src.count(old)}')
src=src.replace(old,'core.iter.adapters.enumerate.IteratorEnumerateMut.enumerate im')
old='ok (context.layout_factor_fingerprint = i)'
if src.count(old)!=15: raise SystemExit('layout equality count')
src=src.replace(old,'ok (decide (context.layout_factor_fingerprint = i))')
old='ok (i = sumcheck.fold_binary_low_masks.CROSS_POSITIONS)'
if src.count(old)!=1: raise SystemExit('cross positions equality count')
src=src.replace(old,'ok (decide (i = sumcheck.fold_binary_low_masks.CROSS_POSITIONS))')
old='field.QM31.ZERO (field.QM31.add)'
if src.count(old)!=1: raise SystemExit('fold function count')
src=src.replace(old,'field.QM31.ZERO (fun p => field.QM31.add p.1 p.2)')
for old,new,count in [
 ('Std.U64.wrapping_shr exp 1#i32','Std.U64.wrapping_shr exp 1#u32',1),
 ('Std.Usize.wrapping_shr low 2#i32','Std.Usize.wrapping_shr low 2#u32',1),
 ('Std.Usize.wrapping_shr tupled_args 2#i32','Std.Usize.wrapping_shr tupled_args 2#u32',1),
 ('Std.U64.wrapping_shr i1 31#i32','Std.U64.wrapping_shr i1 31#u32',1),
 ('Std.U32.wrapping_shl 1#u32 18#i32','Std.U32.wrapping_shl 1#u32 18#u32',1),
]:
 if src.count(old)!=count: raise SystemExit(f'shift form {old}: {src.count(old)}')
 src=src.replace(old,new)
for old,new,count in [
 ('let i3 ← lift (Std.U8.wrapping_shl 1#u8 used_in_last_byte)', 'let used_in_last_byte_u32 ← lift (UScalar.cast .U32 used_in_last_byte)\n      let i3 ← lift (Std.U8.wrapping_shl 1#u8 used_in_last_byte_u32)', 1),
 ('let i5 ← lift (Std.U64.wrapping_shl i4 i2)', 'let i2_u32 ← lift (UScalar.cast .U32 i2)\n    let i5 ← lift (Std.U64.wrapping_shl i4 i2_u32)', 1),
 ('let i ← lift (Std.U16.wrapping_shl 1#u16 low)', 'let low_u32 ← lift (UScalar.cast .U32 low)\n    let i ← lift (Std.U16.wrapping_shl 1#u16 low_u32)', 2),
 ('let i2 ←\n    lift (Std.U32.wrapping_shl 1#u32 v6_query_batch.V6_QUERY_BATCH_TREE_DEPTH)', 'let depth_u32 ←\n    lift (UScalar.cast .U32 v6_query_batch.V6_QUERY_BATCH_TREE_DEPTH)\n  let i2 ←\n    lift (Std.U32.wrapping_shl 1#u32 depth_u32)',1),
]:
 if src.count(old)!=count: raise SystemExit(f'cast form {old!r}: {src.count(old)}')
 src=src.replace(old,new)
# Literal strings elaborate their length proofs through Lean's compiler-native
# decision procedure. These values are used only by generated formatting and
# panic diagnostics. Use the same typed empty diagnostic representation with a
# kernel proof, leaving verifier success/error values unchanged.
src, count = re.subn(r'toStr\s*\"[^\"]*\"', '(⟨[], Nat.zero_le _⟩ : Str)', src)
if count != 9: raise SystemExit(f'toStr literal count: {count}')

for name in [
 'v6_transcript.verify_v7_compact_transcript_and_relation_prepared_with_hiding_context_inner.closure.Insts.CoreOpsFunctionFnMutTupleV6RelationDiagnosticPhaseTuple.call_mut',
 'v6_transcript.verify_v7_compact_transcript_and_relation_prepared_with_hiding_context_snapshot.closure.Insts.CoreOpsFunctionFnMutTupleSharedV6QueryBatchPrechallengeViewTuple.call_mut',
]:
 marker='def\n  '+name
 if src.count(marker)!=1: raise SystemExit(f'callback marker {name}: {src.count(marker)}')
 start=src.index(marker); end=src.find('\n/-- [',start)
 if end<0: raise SystemExit('callback end')
 block=src[start:end]
 body='\n  := do\n  ok c\n'
 if block.count(body)!=1: raise SystemExit(f'callback body {name}: {block.count(body)}')
 result_at=block.rfind('\n  Result\n',0,block.index(body))
 if result_at<0: raise SystemExit('callback result')
 typ=' '.join(block[result_at+len('\n  Result\n'):block.index(body)].split())
 if '.closure' not in typ or 'Unit' in typ: raise SystemExit(f'callback result type {typ}')
 repl='\n  Result (Unit ×\n    '+typ+')\n  := do\n  ok ((), c)\n'
 src=src[:start]+block[:result_at]+repl+block[block.index(body)+len(body):]+src[end:]
if src.count('\n  ok ((), c)\n')!=2: raise SystemExit(f"callback repaired body count: {src.count('\n  ok ((), c)\n')}")
src=src.replace('import V7CallerCurrentReleaseR24.FunsExternal\n', 'import V7CallerCurrentReleaseR24.FunsExternal\nimport V7CallerCurrentReleaseR24.MutableIteratorCompat\n', 1)
out.write_text(src)
print('R24 normalized source-only compatibility: PASS')
