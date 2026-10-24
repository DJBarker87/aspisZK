from pathlib import Path
import re
P=Path('docs/research/100bit-spend-path-20261013/lean')
s=(P/'Port4A_NativeReader.lean').read_text()
s=s[s.index('def tail '):s.index('def resume ')]
a=s.index('              let (a5, r13)');b=s.index('              let r35',a)
s=s[:a]+'''              Port6CK_Queries.cps ops.raw r12 fun queries r34 => do
'''+s[b:]
pattern=r'\(Array.make\s+22#usize\s*\[\s*i8,\s*i9,\s*i10,\s*i11,\s*i12,\s*i13,\s*i14,\s*i15,\s*i16,\s*i17,\s*i18,\s*i19,\s*i20,\s*i21,\s*i22,\s*i23,\s*i24,\s*i25,\s*i26,\s*i27,\s*i28,\s*i29\s*\]\)'
s,n=re.subn(pattern,'queries',s);assert n==2,n
a=s.index('                let r36');b=s.index('\n              | core.ops.control_flow.ControlFlow.Break',a)
suffix='\n'.join(line[14:] if line.startswith(' '*14) else line for line in s[a:b].splitlines())
head='''def suffix (ops : ResumeOps) (bytes : Slice U8) (v : transport.Variant)
    (i4 : U8) (end1 : Usize) (state a3 a4 : Array U8 32#usize)
    (val val1 val2 val3 : aspis_core.field.wide_exact.WideExact) (val4 : aspis_core.field.QM31)
    (queries : Array U32 22#usize) (r34 : verifier.Reader) :
    Result (core.result.Result (verifier.Prepared × verifier.Accumulator) verifier.Error) := do
'''
s=s[:a]+'                suffix ops bytes v i4 end1 state a3 a4 val val1 val2 val3 val4 queries r34'+s[b:]
s=head+suffix+'\n\n'+s
out='''import Port6CK_Queries
import Port4A_NativeReader
set_option autoImplicit false
noncomputable section
namespace AspisR1.Port6CK_Factor
open Aeneas Aeneas.Std Result AspisR1Stage2
'''+s+'''
/-- Literal current source decomposition at its22-query raw-read section. -/
theorem source (ops : ResumeOps) (bytes : Slice U8) (v : transport.Variant)
    (i4 : U8) (end1 : Usize) (s6 : Slice U8) (a2 : Array U8 32#usize) :
    Port4A_NativeReader.tail ops bytes v i4 end1 s6 a2=tail ops bytes v i4 end1 s6 a2 := by
  rfl

#print axioms source
end AspisR1.Port6CK_Factor
end
'''
(P/'Port6CK_Factor.lean').write_text(out)
