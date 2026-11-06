from pathlib import Path
E=Path(__file__).resolve().parent
s=Path('evidence/tx2-native8-20261108/NJU_ResumeObserved.lean').read_text();a=s.index('\ndef run (');b=s.index('\ndef runRef',a);body=s[a:b]
body=body[body.index('  := do')+len('  := do'):]
marker='              let s2 ←';j=body.index(marker);prefix=body[:j]
prefix+='              pure (core.result.Result.Ok (i4,end1))\n'
remaining=body[j:];remaining='\n'.join(l[14:] if l.startswith(' '*14) else l for l in remaining.splitlines())
text='''import NJU_ResumeObserved
import NKK_LogAlgebra
import NKK_Try
set_option autoImplicit false
noncomputable section
namespace NKK_HeaderSource
open Aeneas Aeneas.Std Result AspisR1 NID_ResumeEmission NJU_ResumeObserved

def header {H : Type} (d : AspisR1Stage2.aspis_core.digest.Digest32 H)
 (bytes : Slice U8) (v : transport.Variant) :
 NJU_Log.Run Event (core.result.Result (U8 × Usize) verifier.Error) := do
'''+prefix+'''
def afterHeader (reservation : NP6_StdModel.Reservation) {H : Type}
 (d : AspisR1Stage2.aspis_core.digest.Digest32 H) (bytes proof public1 : Slice U8)
 (v : transport.Variant) (hash : H) (i4 : U8) (end1 : Usize) :
 NJU_Log.Run Event (core.result.Result (verifier.Prepared × verifier.Accumulator) verifier.Error) := do
'''+remaining+'\nend NKK_HeaderSource\n'
E.joinpath('NKK_HeaderSource.lean').write_text(text)
