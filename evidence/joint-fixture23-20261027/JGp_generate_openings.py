from pathlib import Path
import sys
R=Path(__file__).resolve().parents[2]
for i in range(10):
 off=10055+832*i
 name=f'JGp_Opening{i}'
 s=f'''import Port4B_Opening
import JFw_Frames
set_option autoImplicit false
noncomputable section
namespace AspisR1.{name}
open Aeneas Aeneas.Std Result MultiproofConeCanonical
attribute [local irreducible] JFx_NativeBytes.proof JFx_NativeBytes.proofBytes

def value : Slice U8 := JFw_Frames.window {off} 832

theorem length : value.length=832 := JFw_Frames.window_length {off} 832 (by decide)
#print axioms length

theorem source : Port4B_Opening.opening JFx_NativeBytes.proof {i}#usize=ok value := by
  obtain ⟨out,run,size,bytes⟩ := Port4B_Opening.opening_exact JFx_NativeBytes.proof
    (by unfold JFx_NativeBytes.proof;exact JFx_NativeBytes.proofBytes_length) {i}#usize (by decide)
  have same : out=value := by
    apply Subtype.ext
    apply MultiproofConeByteEquality.bytes_injective
    have target := JFw_Frames.window_bytes {off} 832
    exact bytes.trans target.symm
  exact same ▸ run
#print axioms source
end AspisR1.{name}
end
'''
 f=R/f'lean/{name}.lean'
 if '--check' in sys.argv:assert f.read_text()==s,f
 else:f.write_text(s)
print('checked' if '--check' in sys.argv else 'generated','10 actual batch0 opening reads')
