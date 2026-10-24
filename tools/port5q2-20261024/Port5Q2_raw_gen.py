from pathlib import Path
import hashlib,json
R=Path(__file__).resolve().parents[2];E=R/'evidence/port5q2-20261024';L=R/'docs/research/100bit-spend-path-20261013/lean';src=E/'reader-helpers/Funs.lean';s=src.read_text();a=s.index('def verifier.Reader.raw');b=s.index('/--',a)
body=s[a:b].replace('def verifier.Reader.raw','def raw').replace('(N : Std.Usize) (self : verifier.Reader)', '(N : Std.Usize)\n  (unwrap : core.result.Result (Array U8 N) core.array.TryFromSliceError → Result (Array U8 N))\n  (self : verifier.Reader)').replace('core.result.Result.unwrap core.fmt.DebugTryFromSliceError','unwrap')
out='''import Port4A_ReaderInstall
set_option autoImplicit false
noncomputable section
namespace AspisR1.Port5Q2_ReaderRaw
open Aeneas Aeneas.Std Result AspisR1Stage2
'''+body+'''
/-- Local checked/wrapping transport, including all range/conversion failures.
Only addition is guarded; no reader success/output equality is assumed. -/
theorem normalization (N : Usize)
    (unwrap : core.result.Result (Array U8 N) core.array.TryFromSliceError → Result (Array U8 N))
    (r : verifier.Reader) (small : r.at.val+N.val≤4096) :
    raw N unwrap r=verifier.Reader.rawWithUnwrap N unwrap r := by
  unfold raw verifier.Reader.rawWithUnwrap
  rw [Port3_Wrapping.checked_add _ _ small]
  rfl

/-- Actual bounded raw read never reaches the debug-bearing panic handler.
Every possible handler gives the SAME retained reader bytes and cursor. -/
theorem reference (N : Usize)
    (unwrap : core.result.Result (Array U8 N) core.array.TryFromSliceError → Result (Array U8 N))
    (unwrap_ok : ∀ b, unwrap (.Ok b)=ok b)
    (r : verifier.Reader) (bound : r.at.val+N.val≤r.bytes.val.length)
    (size : r.bytes.val.length≤4096) :
    raw N unwrap r=CheckpointBytes3Reader.raw N r := by
  rw [normalization N unwrap r (by omega)]
  obtain ⟨b,out,run,bytes,cursor,backing⟩ := OraclePortCkptAbiReader.raw_total_exact r N unwrap unwrap_ok bound
  obtain ⟨b1,out1,run1,bytes1,cursor1,backing1⟩ :=
    OraclePortCkptAbi2Unwrap.raw_panic_unreachable r N (fun _ => fail .panic) bound
  have hb : b=b1 := Subtype.ext (bytes.trans bytes1.symm)
  have ho : out=out1 := by
    cases out with
    | mk outBytes at1 =>
      cases out1 with
      | mk outBytes1 at2 =>
        simp only [verifier.Reader.mk.injEq]
        exact ⟨backing.trans backing1.symm,UScalar.eq_of_val_eq (cursor.trans cursor1.symm)⟩
  change _=verifier.Reader.rawWithUnwrap N _ r
  rw [run,run1,hb,ho]

#print axioms normalization
#print axioms reference
end AspisR1.Port5Q2_ReaderRaw
end
'''
p=L/'Port5Q2_ReaderRaw.lean';p.write_text(out);(E/'raw-emission.json').write_text(json.dumps({'source_sha256':hashlib.sha256(s.encode()).hexdigest(),'span_start':a,'span_end':b,'span_sha256':hashlib.sha256(s[a:b].encode()).hexdigest(),'module_sha256':hashlib.sha256(out.encode()).hexdigest(),'changes':['native debug-bearing unwrap is a named continuation','current wrapping additions are preserved','namespace/carriers reused from AspisR1Stage2'],'external_template_imported':False},indent=2)+'\n')
