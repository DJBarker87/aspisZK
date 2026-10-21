#!/usr/bin/env python3
"""Factor exactly two emitted read/clone/scan sites; retain the full parent."""
from pathlib import Path
import re,json,hashlib,sys
R=Path(__file__).resolve().parents[2];D=R/'docs/research/100bit-spend-path-20261013/lean-candidates/s126-caller-boundary-20261021'
OutD=Path(sys.argv[1]) if len(sys.argv)>1 else D
OutD.mkdir(exist_ok=True,parents=True)
s=(D/'S2SdkOwnedModelV1.lean').read_text();a=s.index('def owned_stage1_body (ops : Ops)');b=s.index('\ndef owned_stage1 (ops : Ops)')
body=s[a:b];body=body[:body.rfind('/--')] if body.rstrip().endswith('-/') else body
# The following doc block belongs to owned_stage1, not to this body.
body=body[:body.rfind('/--')] if body.rfind('/--')>body.rfind(':=') else body
body=body.rstrip()
pat=r'(?m)^( +)let odc ←\n\s+alloc.vec.Vec.index\n\s+\(core.slice.index.SliceIndexUsizeSlice\n\s+OwnedDataCell\) sdk1.data_cells\n\s+checkpoint.data_slot\n\s+let v ←\n\s+alloc.vec.CloneVec.clone\n\s+core.clone.CloneU8 odc.bytes\n\s+let (b[56]) ← owned_checkpoint_nonzero v'
matched=list(re.finditer(pat,body));assert len(matched)==2,len(matched)
body=re.sub(pat,lambda m:m[1]+'let '+m[2]+' ← scanner sdk1 checkpoint.data_slot',body)
body=body.replace('def owned_stage1_body (ops : Ops)','def bodyWithScan (scanner : OwnedSdk → Usize → Result Bool) (ops : Ops)',1)
head='''-- Complete emitted SDK parent; only two read/clone/scan blocks are factored.
-- The kernel-checked body_factor theorem below validates this fission.
import S2SdkSourceScanV1
import S2SdkOwnedGuardBodyV1
set_option autoImplicit false
noncomputable section
open Aeneas Aeneas.Std Result
namespace AspisS2OwnedStage1.SdkReference.NativeScan
open AspisS2SdkIterator
'''
tail='''

/-- Exact fission of the complete emitted parent, including all statuses,
account metadata, aliases, SDK heap fields, native errors and child calls. -/
theorem body_factor (ops : Ops) (program : Array U8 32#usize)
    (sdk : OwnedSdk) (data : Slice U8) (guards : LiveGuards) :
    owned_stage1_body ops program sdk data guards =
      bodyWithScan snapshotScan ops program sdk data guards := by
  simp only [owned_stage1_body,bodyWithScan,snapshotScan,bind_assoc_eq]
  rfl

/-- Concrete installation of the source-extracted any/SDK-next implementation
in the complete parent. No scan, next, iterator-validity or byte-copy premise
is retained. This remains an owned SDK source reference, not a claim that the
shipped AccountInfo heap construction and all parent steps are already joined. -/
theorem body_eq_source (ops : Ops) (program : Array U8 32#usize)
    (sdk : OwnedSdk) (data : Slice U8) (guards : LiveGuards) :
    owned_stage1_body ops program sdk data guards =
      bodyWithScan sourceScan ops program sdk data guards := by
  rw [body_factor]
  have scans : snapshotScan=sourceScan := funext fun heap => funext fun slot =>
    snapshotScan_eq_sourceScan heap slot
  rw [scans]

def stage1 (ops : Ops) (program : Array U8 32#usize) (sdk : OwnedSdk)
    (data : alloc.vec.Vec U8) :
    Result ((core.result.Result Unit solana_program_error.ProgramError) × OwnedSdk) := do
  let (status,sdkBody,guards) ← bodyWithScan sourceScan ops program sdk
    (alloc.vec.Vec.deref data) {checkpoint:=none,«public»:=none,proof:=none}
  let sdkOut ← owned_release_guards sdkBody guards
  ok (status,sdkOut)

/-- Complete stage1 equality, preserving return status and every SDK field. -/
theorem stage1_eq (ops : Ops) (program : Array U8 32#usize) (sdk : OwnedSdk)
    (data : alloc.vec.Vec U8) :
    stage1 ops program sdk data=owned_stage1 ops program sdk data := by
  unfold stage1 owned_stage1
  rw [←body_eq_source]

/-- The complete source-scan parent establishes its own safe finalization on
all ordinary returns, including errors; no invariant/release premise is added. -/
theorem body_return_finalizes (ops : Ops) (program : Array U8 32#usize)
    (sdk sdkBody : OwnedSdk) (data : alloc.vec.Vec U8)
    (status : core.result.Result Unit solana_program_error.ProgramError) (guards : LiveGuards)
    (body : bodyWithScan sourceScan ops program sdk (alloc.vec.Vec.deref data)
      GuardAcquire.noGuards=ok (status,sdkBody,guards)) :
    ∃ sdkOut, stage1 ops program sdk data=ok (status,sdkOut) := by
  have original := (body_eq_source ops program sdk (alloc.vec.Vec.deref data)
    GuardAcquire.noGuards).trans body
  obtain ⟨sdkOut,hrun⟩ := GuardBody.body_return_finalizes ops program sdk sdkBody
    data status guards original
  exact ⟨sdkOut,(stage1_eq ops program sdk data).trans hrun⟩

/-- Complete source-scan adapter success derives the actual same-byte first
caller, decoded statement and fixed compact split, with release None. -/
theorem stage1_current_first_split (ops : SdkReference.Ops) (verifierOps : AspisR1CurrentCaller.Ops)
    (program : Array U8 32#usize) (sdk sdkOut : OwnedSdk) (data : alloc.vec.Vec U8)
    (h : stage1 (Installation.install ops verifierOps) program sdk data=ok (.Ok (),sdkOut)) :
    ∃ (publicBytes : Slice U8) (decoded : AspisR1TerminalDecoder.PublicBinding.Statement)
      (proofBytes : Slice U8) (out : alloc.vec.Vec U8),
      AspisR1PublicPreparation.S6DecoderScopedReuseV1.decodeActual publicBytes=ok (.Ok decoded) ∧
      AspisR1CurrentCaller.FirstComposition.firstCurrent
        solana_program_error.ProgramError.InvalidAccountData verifierOps
        (SourceInstallation.currentDigest
          (SolanaDigest.Insts.Aspis_coreDigestDigest32 (Installation.install ops verifierOps)))
        (fun e => ops.op11 (SourceInstallation.freshError e)) publicBytes proofBytes 10#usize=ok (.Ok out) := by
  apply DecodedReuse.stage1_current_first_split ops verifierOps program sdk sdkOut data
  exact (stage1_eq (Installation.install ops verifierOps) program sdk data).symm.trans h

#print axioms stage1_current_first_split

#print axioms body_return_finalizes

#print axioms body_factor
#print axioms body_eq_source
#print axioms stage1_eq
end AspisS2OwnedStage1.SdkReference.NativeScan
'''
out=head+body+tail
(OutD/'S2SdkNativeScanParentV1.lean').write_text(out)
sha=lambda s:hashlib.sha256(s.encode()).hexdigest()
(OutD/'sdk-native-scan-parent-fission.json').write_text(json.dumps(dict(schema='focused-extractor-proof-packet-v1',emitted_model_sha256=sha(s),source_sha256=sha(out),factored_blocks=[dict(source=m[0],sha256=sha(m[0])) for m in matched],qualification='Only exact two-site fission plus scanner parameterization. body_factor must compile to validate the complete parent equivalence. All original caller branches and carriers are retained.'),indent=2)+'\n')
