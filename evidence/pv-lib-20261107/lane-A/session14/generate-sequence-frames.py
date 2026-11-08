from pathlib import Path
import re
sources=[('PV_LIB_A_F6SourceSequences14','seq'+c) for c in 'ABCDE']+[(m,'seq') for m in ['PV_LIB_A_F125Prologue13','PV_LIB_A_F219Prologue13','PV_LIB_A_F219CallbackHistory14','PV_LIB_A_CallbackTail14','PV_LIB_A_F316Prefix13','PV_LIB_A_F316ToInvoke13','PV_LIB_A_F220Prefix14','PV_LIB_A_F208Prefix14']]
s=''.join('import '+m+'\n' for m in dict.fromkeys(m for m,_ in sources))+'''import PV_LIB_A_SequenceFrame14
import PV_LIB_A_RangeInvariant12
set_option autoImplicit false
noncomputable section
namespace PV_LIB_A_PrefixSequenceFrames14
open PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine PV_EVHB_OwnerMachine
open PV_LIB_A_SourceCellFrame14 PV_LIB_A_SourceSequence13
'''
for i,(m,n) in enumerate(sources):
 raw=Path('lean',m+'.lean').read_text();a=raw.index('def '+n+' :');b=raw.index('theorem shape',a)
 nodes=list(dict.fromkeys(re.findall(r'PV_THR2_\w+\.node\d+',raw[a:b])))
 s+=f'''\n/-- Exact emitted source moves/destinations; metadata is not evaluated. -/
theorem safe{i} : PV_LIB_A_SequenceFrame14.Safe {m}.{n} := by
  simp [{m}.{n},PV_LIB_A_SequenceFrontier13.prepend,
    {', '.join(nodes)},
    PV_LIB_A_SequenceFrame14.Safe,PV_LIB_A_ExpressionFrame14.Safe,
    PV_LIB_A_OperandFrame14.Safe,Local]
#print axioms safe{i}
'''
s+='''
/-- Derive the iterator facet through any certified callee SOURCE sequence,
including its missing-binding arm. Actual prefix certificates are safe0..safe12.
Older/younger activation ordering is the live-numbering obligation, never an
activation-counter identity across a callee boundary. Native/OWNER frames are
separate obligations and are not hidden in this theorem. -/
theorem iterator (C : Carrier OWNER Data) (s : Store Data) (caller child start finish : Nat)
    (parents : List Frame) (loops : List LoopFrame) (rest : List PV_STX2_SliceSyntax.Node)
    (w : OWNER) (seq : Seq) (safe : PV_LIB_A_SequenceFrame14.Safe seq)
    (younger : caller < child) (before : PV_LIB_A_RangeInvariant12.Iterator s caller start finish) :
    PV_LIB_A_RangeInvariant12.Iterator
      (PV_LIB_A_SequenceFrame14.storeOf (result C child parents loops rest w seq s)) caller start finish := by
  have frame := PV_LIB_A_SequenceFrame14.result_frame C (caller+1) s child parents loops rest w seq
    (by omega) safe
  unfold PV_LIB_A_RangeInvariant12.Iterator
  rw [frame ⟨caller,7,[]⟩ (by simp)]
  exact before

#print axioms iterator
end PV_LIB_A_PrefixSequenceFrames14
'''
Path('lean/PV_LIB_A_PrefixSequenceFrames14.lean').write_text(s)
