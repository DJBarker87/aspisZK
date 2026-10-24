#!/usr/bin/env python3
"""Reuse proof patterns against actual native functions; no Rust/function rewrite."""
from pathlib import Path
import hashlib,json,sys
R=Path(__file__).resolve().parents[2];B=R/'docs/research/100bit-spend-path-20261013';S=B/'lean-candidates/s126-caller-boundary-20261021';E=B/'evidence/s126-current-caller-20261021';rows={}
for old,new,imports in [
 ('S6SourcePaymentDecodeHelpersV1','S6NativePaymentDecodeHelpersV1',['S6NativeDigestAcceptedInverseV1','S6NativePaymentValidatorTotalV1']),
 ('S6SourcePaymentCommonDecodeV1','S6NativePaymentCommonDecodeV1',['S6NativePaymentDecodeHelpersV1','S6ByteInverseV1']),
 ('S6SourcePaymentHeaderTotalV1','S6NativePaymentHeaderTotalV1',['S6NativePaymentCommonDecodeV1','S6StdByteSliceEqualityV1']),
 ('S6SourcePaymentDecodeTotalV1','S6NativePaymentDecodeTotalV1',['S6NativePaymentHeaderTotalV1']),
 ('S6SourcePaymentDecodedFramesV1','S6NativePaymentDecodedFramesV1',['S6NativePaymentDecodeTotalV1']),
 ('S6SourcePaymentCommonContentsV1','S6NativePaymentCommonContentsV1',['S6NativePaymentDecodedFramesV1','S6PaymentCommonChunkFrameV1']),
 ('S6PaymentFrameRecomposeV1','S6NativePaymentFrameRecomposeV1',['S6NativePaymentCommonContentsV1','S6SliceRecomposeV1']),
 ('S6PaymentCommonOutputV1','S6NativePaymentCommonOutputV1',['S6NativePaymentCommonContentsV1','S6NativePaymentCommonEncodeTotalV1']),
 ('S6SourcePaymentWriterContentsV1','S6NativePaymentWriterContentsV1',['S6NativePaymentFrameRecomposeV1','S6NativePaymentCommonOutputV1','S6PaymentTailChunkFrameV1']),
 ('S6SourcePaymentAcceptedInverseV1','S6NativePaymentAcceptedInverseV1',['S6NativePaymentWriterContentsV1','S6ZeroWordBytesV1','S6NativePaymentEncodeTotalV1'])]:
 original=S/(old+'.lean');text=original.read_text();text='\n'.join(line for line in text.splitlines() if not line.startswith('import '))+'\n'
 text=''.join('import '+name+'\n' for name in imports)+text
 text=text.replace('AspisS6SourceCodec.PaymentContents','AspisS6NativePaymentContents').replace('DigestContents.encode_contents','AspisS6NativeSnapshotEncodeTotal.digest_spec').replace('DigestContents.chunks','AspisS6SourceCodec.DigestContents.chunks')
 import re
 text=re.sub(r'(?<![\w.])PaymentDecode\.', 'AspisS6NativePaymentDecode.',text)
 text=re.sub(r'(?<![\w.])PaymentEncodeTotal\.', 'AspisS6NativePaymentEncodeTotal.',text)
 text=text.replace('AspisS6SourceCodec.PaymentDecodeHelpers','AspisS6NativePaymentDecodeHelpers').replace('AspisS6SourceCodec.PaymentDecode','AspisS6NativePaymentDecode')
 text=text.replace('open AspisS6FiveUnrolledCodec','open AspisR1TerminalDecoder').replace('aspis_statement.','')
 if new=='S6NativePaymentDecodeHelpersV1':
  text=text.replace('end AspisS6NativePaymentDecodeHelpers',''.join('#print axioms map_'+str(i)+'_spec\n' for i in range(7))+'end AspisS6NativePaymentDecodeHelpers')
 text=text.replace('PaymentTotal.transfer_total','AspisS6NativePaymentValidatorTotal.transfer_total').replace('PaymentTotal.withdrawal_total','AspisS6NativePaymentValidatorTotal.withdrawal_total')
 if new=='S6NativePaymentDecodedFramesV1':
  text=text.replace('simp_all [transfer_common,List.slice]','simp_all [transfer_common,List.slice,AspisS6NativeDigestEncodeSourceEq.encode_eq]').replace('simp_all [withdrawal_common,List.slice,','simp_all [withdrawal_common,List.slice,AspisS6NativeDigestEncodeSourceEq.encode_eq,')
 if new=='S6NativePaymentCommonDecodeV1':
  text=text.replace('simp_all [common_frame,','simp_all [common_frame,AspisS6NativeDigestEncodeSourceEq.encode_eq,')
 target=S/(new+'.lean')
 if '--check' in sys.argv:assert target.read_text()==text
 else:target.write_text(text)
 rows[new]=dict(reused_proof=str(original.relative_to(R)),reused_sha256=hashlib.sha256(original.read_bytes()).hexdigest(),native_sha256=hashlib.sha256(text.encode()).hexdigest())
meta=dict(schema='focused-extractor-proof-packet-v1',targets=rows,qualification='Migrates existing proof patterns to original native functions and complete native records; no source function or Rust rewrite. Each new proof must kernel-check independently before acceptance.')
p=E/'s6-native-payment-proof-reuse.json'
if '--check' in sys.argv:assert json.loads(p.read_text())==meta
else:p.write_text(json.dumps(meta,indent=2)+'\n')
