from pathlib import Path
import hashlib,json
R=Path(__file__).resolve().parents[2];E=R/'evidence/port5q2-20261024';L=R/'docs/research/100bit-spend-path-20261013/lean';s=(E/'reader-helpers/Funs.lean').read_text();out='''import Port5Q2_ReaderRaw
import Port1_LibrarySource
set_option autoImplicit false
noncomputable section
namespace AspisR1.Port5Q2_ReaderScalar
open Aeneas Aeneas.Std Result AspisR1Stage2
abbrev Raw := (N : Usize) → verifier.Reader → Result (Array U8 N × verifier.Reader)
''';spans=[]
for kind,ty,decoder in [('k','aspis_core.field.QM31','aspis_core.field.QM31.from_le_bytes'),('e','aspis_core.field.wide_exact.WideExact','aspis_core.field.wide_exact.WideExact.from_le_bytes')]:
 a=s.index('def verifier.Reader.'+kind+'\n');b=s.index('/--',a)
 body=s[a:b].replace('def verifier.Reader.'+kind,f'def read{kind.upper()} (raw : Raw) (decode : Slice U8 → Result (Option {ty}))').replace('verifier.Reader.raw','raw').replace(decoder,'decode').replace('core.option.Option.ok_or','Port1_LibrarySource.okOr')
 out+=body;spans.append({'kind':kind,'start':a,'end':b,'sha256':hashlib.sha256(s[a:b].encode()).hexdigest()})
 out+=f'''def decode{kind.upper()} (s : Slice U8) : Result (Option {ty}) := do
  let value ← OraclePortCkptAbi2Extracted.decode_{kind}_spec s
  ok (value.map CheckpointBytes3Namespaces.from{kind.upper()})

theorem reference_{kind} (r : verifier.Reader) :
    read{kind.upper()} CheckpointBytes3Reader.raw decode{kind.upper()} r=CheckpointBytes3Reader.read{kind.upper()} r := by
  unfold read{kind.upper()} decode{kind.upper()} CheckpointBytes3Reader.read{kind.upper()}
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro pair success
  rcases pair with ⟨bytes,out⟩
  try dsimp only
  simp only [lift,bind_tc_ok,Aeneas.Std.uncurry,bind_assoc_eq]
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro value decoded
  cases value <;> rfl

#print axioms reference_{kind}
'''
for kind,width in [('k',16),('e',32)]:
 out+=f'''
/-- Bounded CURRENT scalar helper with an arbitrary debug panic handler.
The field codec is the separately certified concrete content interpretation. -/
theorem current_{kind}
    (unwrap : (N : Usize) → core.result.Result (Array U8 N) core.array.TryFromSliceError → Result (Array U8 N))
    (unwrap_ok : ∀ N b, unwrap N (.Ok b)=ok b)
    (r : verifier.Reader) (bound : r.at.val+{width}≤r.bytes.val.length)
    (size : r.bytes.val.length≤4096) :
    read{kind.upper()} (fun N => Port5Q2_ReaderRaw.raw N (unwrap N)) decode{kind.upper()} r=CheckpointBytes3Reader.read{kind.upper()} r := by
  rw [← reference_{kind} r]
  unfold read{kind.upper()}
  dsimp only
  rw [Port5Q2_ReaderRaw.reference {width}#usize (unwrap {width}#usize) (unwrap_ok {width}#usize) r bound size]

#print axioms current_{kind}
'''
out+='end AspisR1.Port5Q2_ReaderScalar\nend\n';(L/'Port5Q2_ReaderScalar.lean').write_text(out);(E/'scalar-emission.json').write_text(json.dumps({'source_sha256':hashlib.sha256(s.encode()).hexdigest(),'spans':spans,'module_sha256':hashlib.sha256(out.encode()).hexdigest(),'changes':['raw reader and field from_le_bytes are explicit leaves','namespace/carriers reused from AspisR1Stage2'],'external_template_imported':False},indent=2)+'\n')
