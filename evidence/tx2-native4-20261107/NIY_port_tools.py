from pathlib import Path
import re
E=Path(__file__).resolve().parent

def params(mod,fn):
 s=(E/(mod+'.lean')).read_text();a=s.index('(reserved : Bool)',s.index('def '+fn));b=s.index(' :\n Result',a);return s[a:b]
def context(p):
 p=p[p.index(' (state :'):];return [(n.strip(),t.strip()) for n,t in re.findall(r'\((\w+) : ([^()]+)\)',p)]
def conv(n,t):
 if t=='aspis_core.field.wide_exact.WideExact':return '(e '+n+')'
 if t=='aspis_core.field.QM31':return '(k '+n+')'
 if t.startswith('Array aspis_core.field.QM31'):return '(array k '+n+')'
 if t.startswith('alloc.vec.Vec aspis_core.field.QM31'):return '(vec k '+n+')'
 if t=='verifier.Reader':return '(reader '+n+')'
 return n

def head(ns,imports):return ''.join('import '+m+'\n' for m in imports)+f'''set_option autoImplicit false
noncomputable section
namespace {ns}
open Aeneas Aeneas.Std Result NIL_Carriers NIL_ResultTransport NIL_ResultReverse AspisR1
open NID_ResumeEmission
'''
def statement(mod,fn):
 p=params(mod,fn);ctx=context(p);fa=' '.join(n for n,t in ctx);ca=' '.join(conv(n,t) for n,t in ctx);cm='NIY_C_'+mod.removeprefix('NIY_')
 return p,ctx,fa,ca,f''' NIL_StatePort.reply ({mod}.{fn} reserved d bytes v end1 i4 {fa})=
 {cm}.{fn} (CheckpointBytes4Ops.ops reserved) bytes (variant v) end1 i4 {ca}'''
if __name__=='__main__':
 ns='NIY_WeightsPort';p,ctx,fa,ca,st=statement('NIY_AllocationCut','suffix')
 # Parameters before the allocated Vec and reader are common to the final cut.
 common=' '.join(n for n,t in ctx if n not in ['val13','r50'])
 out=head(ns,['NIY_FinalPort','NIY_SectionBind'])+'\ntheorem source '+p+' :\n'+st+''' := by
 with_unfolding_all rw [NIY_FinalCut.source,NIY_C_FinalCut.source]
 unfold NIL_StatePort.reply NIL_FreshOps.weights
 apply NIY_SectionBind.sectionReply
 rintro ⟨weights,at2⟩
 have h := NIY_FinalPort.source reserved d bytes v end1 i4 '''+common+''' (vec unK weights) at2 r50
 simpa only [vec_roundtrip unK k k_reverse] using h
#print axioms source
end '''+ns+'\n'
 (E/(ns+'.lean')).write_text(out)
 print('Authored exact weights port using SAME weights/offset reply and retained final-field transport.')
