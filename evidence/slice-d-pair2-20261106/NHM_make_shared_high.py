from pathlib import Path
import subprocess,hashlib,json
E=Path(__file__).resolve().parent
path='evidence/finish-install2-20261026/FIo_014/sources/FIo_NativeFuns.lean'
s=subprocess.check_output(['git','show','HEAD:'+path],text=True)
a=s.index('def _root_.FIo_Native.weights.shared_high\n');b=s.index('\n/--',a)
ref=s[a:b].replace('def _root_.FIo_Native.weights.shared_high','def reference').replace('_root_.FIo_Native.weights.high_dot','NHM_HighDot.reference')
out='''import NHM_HighDot
set_option autoImplicit false
noncomputable section
namespace NHM_SharedHigh
open Aeneas Aeneas.Std Result ControlFlow AspisR1 LPi_FieldValues FIo_Native
'''+ref+'''

/-- Two SAME high_dot calls and the exact first-error/parts[1]/parts[3] chain.
Scalar/product packets remain explicit in the suffix; native parent cuts OPEN. -/
theorem cohort (partials : Array NE 4#usize) (w : FIo_Native.weights.Weights)
 (ap0 ap1 : Array NE 4#usize) (parts : Array NE 7#usize) :
 FIo_Native.weights.shared_high partials w ap0 ap1 parts=reference partials w ap0 ap1 parts := by
 unfold FIo_Native.weights.shared_high reference
 simp only [NHM_HighDot.cohort]
 rfl

#print axioms cohort
end NHM_SharedHigh
end
'''
(E/'NHM_SharedHigh.lean').write_text(out)
(E/'NHM_SHARED_HIGH_INPUT.json').write_text(json.dumps(dict(path=path,sha256=hashlib.sha256(s.encode()).hexdigest(),changes='Only callee name high_dot -> reference; theorem checked against actual selected definition; no child success premise'),indent=2)+'\n')
