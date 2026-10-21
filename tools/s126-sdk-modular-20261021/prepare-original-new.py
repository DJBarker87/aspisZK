#!/usr/bin/env python3
"""Bind exact frozen Prepared.new emission, with all complete retained carriers."""
from pathlib import Path
import re,json,hashlib
R=Path(__file__).resolve().parents[2];B=R/'docs/research/100bit-spend-path-20261013';S=B/'lean-candidates/s126-caller-boundary-20261021';I=B/'evidence/s126-current-caller-20261021/host/prepared-v7/generated/AspisR1CurrentCaller'
s=(I/'Funs.lean.txt').read_text();a=s.index('def verifier.Prepared.new\n');b=s.index('\n/--',a);raw=s[a:b]
# Every replacement is a declared identifier, never a body/control-flow change.
mapping={'verifier.Prepared.new':'OriginalPreparedNative.prepare B','aspis_core.digest.Digest32':'aspis_core.Digest32','aspis_core.field.wide_exact.WideExact.to_le_bytes':'B.sampling.toBytes','aspis_core.field.wide_exact.WideExact.ZERO':'OriginalPreparedNative.zero','aspis_core.field.wide_exact.WideExact':'aspis_core.field.WideExact','transcript.Transcript.scalar_k':'PreparedModel.scalar_k B.sampling','transcript.Transcript.scalar':'PreparedModel.scalar B.sampling','transcript.Transcript.queries':'B.sampling.queries','weights.powers':'B.powers','verifier.prepared_claim':'B.claim'}
pat=re.compile(r'(?<![A-Za-z0-9_.])(?:'+'|'.join(re.escape(n) for n in sorted(mapping,key=len,reverse=True))+r')(?![A-Za-z0-9_.])')
body=pat.sub(lambda m:mapping[m[0]],raw);body=body.replace('def OriginalPreparedNative.prepare B\n','def OriginalPreparedNative.prepare (B : PreparedScratchModel.Boundaries)\n',1)
header='''import CurrentCompactInstalledPreparationV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow
namespace AspisR1PublicPreparation
namespace OriginalPreparedNative
/-- Actual source zero under the complete retained field carrier. -/
def zero : Result aspis_core.field.WideExact := ok aspis_core.field.WideExact.ZERO
end OriginalPreparedNative
'''
tail='''
/-- Complete Result and scratch equality, including both error branches,
query rejection before scratch replacement, and claim rejection after it.
No success, canonicality, totality or output equation premise. The fields of B
are explicit child boundaries, not assertions of concrete child installation. -/
theorem OriginalPreparedNative.eq_prepare (B : PreparedScratchModel.Boundaries)
    {H : Type} (D : aspis_core.Digest32 H) (sem : r1_semantic.Verified H)
    (v : verifier.View) (hash : H) (g : Array aspis_core.field.WideExact 29#usize) :
    OriginalPreparedNative.prepare B D sem v hash g=
      PreparedScratchModel.prepare B D sem v hash g := by
  unfold OriginalPreparedNative.prepare PreparedScratchModel.prepare OriginalPreparedNative.zero
  simp only [bind_tc_ok]
  rfl

#print axioms OriginalPreparedNative.prepare
#print axioms OriginalPreparedNative.eq_prepare
end AspisR1PublicPreparation
'''
out=header+body+tail;(S/'CurrentOriginalPreparedNativeV1.lean').write_text(out)
sha=lambda s:hashlib.sha256(s.encode()).hexdigest()
(S/'original-prepared-native-adapter.json').write_text(json.dumps(dict(schema='focused-extractor-proof-packet-v1',source_revision='b2727acd3abf79315d18b754a260f58f4b1c6326',raw_emission=str(I/'Funs.lean.txt'),raw_body_sha256=sha(raw),identifier_map=mapping,added_binder='B : PreparedScratchModel.Boundaries',bound_body_sha256=sha(body),qualification='Full retained source carriers under explicit coordinate-preserving renaming. This equality closes fresh emitted body versus retained scratch model only; concrete child installation and current-carrier transport are separate.'),indent=2)+'\n')
