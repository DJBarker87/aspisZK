from pathlib import Path
import hashlib,json,argparse
ap=argparse.ArgumentParser();ap.add_argument("--check",action="store_true");args=ap.parse_args()
tool=Path(__file__).resolve().parent;area=tool.parents[1];raw=(tool/'retained-resume-fields-generated/Funs.lean').read_text();body=raw[raw.index('def begin_fields'):raw.index('end AspisR1RetainedResumeFields')].replace('def begin_fields','def retained_begin_fields').replace('ResumeReader.e','retained_read_e')
p=area/'lean/CuSavingsRetainedResumeSource.lean'
pre='''import AspisR1RhoResumeCaller.Funs
import CuSavingsCanonicalReader
import CuSavingsCanonicalKReader
import CuSavingsLibraOrigins
set_option autoImplicit false
namespace AspisR1RhoResumeCaller
open Aeneas Aeneas.Std Result ControlFlow
structure ResumeHeader where
  r : ResumeReader
  «end» : Usize
  state : Array U8 32#usize
  roots : Array (Array U8 32#usize) 2#usize

def retained_to_reader (r : ResumeReader) : AspisR1CanonicalReader.Reader := ⟨r.bytes,r.«at»⟩
def retained_from_reader (r : AspisR1CanonicalReader.Reader) : ResumeReader := ⟨r.bytes,r.«at»⟩
def retained_e (e : AspisR1CanonicalReader.field.wide_exact.WideExact) : aspis_core.field.WideExact :=
  ⟨⟨⟨e.c0.c0.a,e.c0.c0.b⟩,⟨e.c0.c1.a,e.c0.c1.b⟩⟩,⟨⟨e.c1.c0.a,e.c1.c0.b⟩,⟨e.c1.c1.a,e.c1.c1.b⟩⟩⟩
def retained_error (e : AspisR1CanonicalReader.Error) : verifier.Error :=
  match e with
  | .Parse => .Parse | .Semantic => .Semantic | .Transcript => .Transcript | .Relation => .Relation
  | .Merkle => .Merkle | .Query => .Query | .Checkpoint => .Checkpoint | .Allocation => .Allocation

def retained_read_e [AspisR1CanonicalReader.Runtime] (r : ResumeReader) :
    Result (core.result.Result aspis_core.field.WideExact verifier.Error × ResumeReader) := do
  let (v,after) ← AspisR1CanonicalReader.Reader.e (retained_to_reader r)
  .ok ((match v with | .Ok value => .Ok (retained_e value) | .Err error => .Err (retained_error error)),retained_from_reader after)

variable [AspisR1CanonicalReader.Runtime]
'''
text=pre+body+'\n#print axioms retained_begin_fields\nend AspisR1RhoResumeCaller\n'
if args.check:assert p.read_text()==text
else:p.write_text(text)
data=json.dumps(dict(raw_begin_body_sha256=hashlib.sha256(body.encode()).hexdigest(),source_sha256=hashlib.sha256(p.read_bytes()).hexdigest(),source_nominal_carriers='Original RhoResumeCaller aliases, exact same source E/K/Reader/ResumeBegin carriers',normalization='Only begin_fields renamed retained_begin_fields and checked concrete Reader.e binding renamed retained_read_e. Namespace promoted. All four actual emitted read/control/error branches unchanged.'),indent=2)+'\n'
if args.check:assert (tool/'retained-resume-fields-emission.json').read_text()==data
else:(tool/'retained-resume-fields-emission.json').write_text(data)
print(json.dumps({'check':args.check,'source_sha256':hashlib.sha256(p.read_bytes()).hexdigest()}))
