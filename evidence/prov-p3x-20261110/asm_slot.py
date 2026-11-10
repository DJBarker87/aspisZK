import re
F=open('PCWF_E001_emitted/raw/PCWF_slot/Funs.lean').read()
a=F.index('namespace PCWF_slot')+len('namespace PCWF_slot'); b=F.index('end PCWF_slot')
body=F[a:b]
body=re.sub(r'@\[rust_loop_body\]\n','',body); body=re.sub(r'@\[rust_loop\]\n','',body)
assert 'rust_' not in body.replace('aspis_r1_cost_probe','')
hdr='''-- PCWF item C (NGD_SlotRef): fresh 4bb3b3f emission PCWF_E001 (aspis-r1-cost-probe compact.rs, overflow-checks OFF, root crate::compact::slot_offset)
-- against the gate NGD_SlotRef.Funs. Gate constant OFF_NODES : Usize := 28359 is a literal; the frozen constant is the Result chain below.
import Aeneas
import NGD_SlotRef.Funs
open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000
set_option maxRecDepth 2048
noncomputable section
namespace NGD_SlotRef
namespace PRVFresh_NGD_SlotRef
'''
# literal chain
ops=[]  # (fresh def, [(a,op,b,c)])
chain={'verifier.SEMANTIC_BYTES':[(29,'*',32,928),(12903,'+',928,13831)],
'compact.SEMANTIC_COMPACT_VALUES':[(10,'*',28,280),(1,'+',280,281),(87,'+',29,116),(281,'+',116,397),(397,'+',29,426)],
'compact.COMPACT_SEMANTIC':[(16,'*',426,6816),(13831,'-',6816,7015)],
'compact.COMPACT_Y1':[(29,'*',16,464)],
'compact.OPENING':[(480,'+',128,608),(608,'+',32,640),(640,'+',32,672),(672,'+',128,800),(800,'+',32,832)],
'compact.OFF_Y1':[(16,'+',7015,7031)],
'compact.OFF_INACTIVE':[(7031,'+',464,7495)],
'compact.OFF_ROUND0':[(7495,'+',32,7527)],
'compact.OFF_FOLDED_ROOT':[(7527,'+',224,7751)],
'compact.OFF_ROUND1':[(7751,'+',32,7783)],
'compact.OFF_FINAL':[(7783,'+',224,8007)],
'compact.OFF_OPENINGS':[(64,'*',32,2048),(8007,'+',2048,10055)],
'compact.OFF_NODES':[(22,'*',832,18304),(10055,'+',18304,28359)]}
val={'verifier.SEMANTIC_BYTES':13831,'compact.LOGICAL_SEMANTIC':13831,'compact.SEMANTIC_COMPACT_VALUES':426,'compact.COMPACT_SEMANTIC':7015,'compact.COMPACT_Y1':464,'compact.OPENING':832,'compact.OFF_Y1':7031,'compact.OFF_INACTIVE':7495,'compact.OFF_ROUND0':7527,'compact.OFF_FOLDED_ROOT':7751,'compact.OFF_ROUND1':7783,'compact.OFF_FINAL':8007,'compact.OFF_OPENINGS':10055,'compact.OFF_NODES':28359}
lem='''
theorem lit_add (a b c : Std.Usize) (h : a.val + b.val = c.val) : (a + b : Result Std.Usize) = ok c := by
  have hmax : a.val + b.val ≤ Std.Usize.max := by scalar_tac
  obtain ⟨z, hz, hv⟩ := Aeneas.Std.WP.spec_imp_exists (Usize.add_spec (x := a) (y := b) hmax)
  rw [hz]; congr 1; apply UScalar.eq_of_val_eq; omega

theorem lit_mul (a b c : Std.Usize) (h : a.val * b.val = c.val) : (a * b : Result Std.Usize) = ok c := by
  have hmax : a.val * b.val ≤ Std.Usize.max := by scalar_tac
  obtain ⟨z, hz, hv⟩ := Aeneas.Std.WP.spec_imp_exists (Usize.mul_spec (x := a) (y := b) hmax)
  rw [hz]; congr 1; apply UScalar.eq_of_val_eq; omega

theorem lit_sub (a b c : Std.Usize) (h : a.val - b.val = c.val) (hle : b.val ≤ a.val) : (a - b : Result Std.Usize) = ok c := by
  obtain ⟨z, hz, hv⟩ := Aeneas.Std.WP.spec_imp_exists (Usize.sub_spec (x := a) (y := b) hle)
  rw [hz]; congr 1; apply UScalar.eq_of_val_eq; omega
'''
out=hdr+body.strip('\n')+'\n\nend PRVFresh_NGD_SlotRef\nend NGD_SlotRef\n'+lem
def L(n):return f'{n}#usize'
th=[]
order=['verifier.SEMANTIC_BYTES','compact.LOGICAL_SEMANTIC','compact.SEMANTIC_COMPACT_VALUES','compact.COMPACT_SEMANTIC','compact.COMPACT_Y1','compact.OPENING','compact.OFF_Y1','compact.OFF_INACTIVE','compact.OFF_ROUND0','compact.OFF_FOLDED_ROOT','compact.OFF_ROUND1','compact.OFF_FINAL','compact.OFF_OPENINGS','compact.OFF_NODES']
defs={'compact.LOGICAL_SEMANTIC':['verifier.SEMANTIC_BYTES'],'compact.COMPACT_SEMANTIC':['compact.SEMANTIC_COMPACT_VALUES','compact.LOGICAL_SEMANTIC'],'compact.OFF_Y1':['compact.COMPACT_SEMANTIC','compact.OFF_SEMANTIC'],'compact.OFF_INACTIVE':['compact.OFF_Y1','compact.COMPACT_Y1'],'compact.OFF_ROUND0':['compact.OFF_INACTIVE'],'compact.OFF_FOLDED_ROOT':['compact.OFF_ROUND0'],'compact.OFF_ROUND1':['compact.OFF_FOLDED_ROOT'],'compact.OFF_FINAL':['compact.OFF_ROUND1'],'compact.OFF_OPENINGS':['compact.OFF_FINAL','compact.FINAL_LEN'],'compact.OFF_NODES':['compact.OPENING','compact.OFF_OPENINGS','compact.QUERIES']}
vname=lambda n:'v_'+n.replace('.','_')
consts='''
theorem c_HEADER : NGD_SlotRef.PRVFresh_NGD_SlotRef.compact.HEADER = 16#usize := by delta NGD_SlotRef.PRVFresh_NGD_SlotRef.compact.HEADER; rfl
theorem c_QUERIES : NGD_SlotRef.PRVFresh_NGD_SlotRef.compact.QUERIES = 22#usize := by delta NGD_SlotRef.PRVFresh_NGD_SlotRef.compact.QUERIES; rfl
theorem c_FINAL_LEN : NGD_SlotRef.PRVFresh_NGD_SlotRef.compact.FINAL_LEN = 64#usize := by delta NGD_SlotRef.PRVFresh_NGD_SlotRef.compact.FINAL_LEN; rfl
theorem c_OFF_SEMANTIC : NGD_SlotRef.PRVFresh_NGD_SlotRef.compact.OFF_SEMANTIC = 16#usize := by
  delta NGD_SlotRef.PRVFresh_NGD_SlotRef.compact.OFF_SEMANTIC; exact c_HEADER
'''
out+=consts
P='NGD_SlotRef.PRVFresh_NGD_SlotRef.'
for n in order:
    haves=[]
    for i,(a,op,b,c) in enumerate(chain.get(n,[])):
        lem_={'+':'lit_add','*':'lit_mul','-':'lit_sub'}[op]
        extra=' (by scalar_tac)' if op=='-' else ''
        haves.append(f'  have h{i} : ({L(a)} {op} {L(b)} : Result Std.Usize) = ok {L(c)} := {lem_} _ _ _ (by scalar_tac){extra}')
    simp=['h%d'%i for i in range(len(chain.get(n,[])))]
    callees=[vname(d) for d in defs.get(n,[]) if d in val]+[ 'c_'+d.split('.')[-1] for d in defs.get(n,[]) if d in ('compact.OFF_SEMANTIC','compact.FINAL_LEN','compact.QUERIES')]
    s=simp+callees+['bind_tc_ok']
    out+=f'\ntheorem {vname(n)} : {P}{n} = ok {L(val[n])} := by\n  delta {P}{n}\n'+'\n'.join(haves)+('\n' if haves else '')+f'  simp only [{", ".join(s)}]\n'
out+=f'''
theorem PRVEq.NGD_SlotRef.Funs.OFF_NODES : {P}compact.OFF_NODES = ok NGD_SlotRef.OFF_NODES := by
  rw [v_compact_OFF_NODES]; delta NGD_SlotRef.OFF_NODES; rfl
#print axioms PRVEq.NGD_SlotRef.Funs.OFF_NODES

theorem PRVEq.NGD_SlotRef.Funs.SLOT_NODES : {P}compact.SLOT_NODES = NGD_SlotRef.SLOT_NODES := by
  delta {P}compact.SLOT_NODES NGD_SlotRef.SLOT_NODES; rfl
#print axioms PRVEq.NGD_SlotRef.Funs.SLOT_NODES

theorem PRVEq.NGD_SlotRef.Funs.slot_offset_loop.body : @{P}compact.slot_offset_loop.body = @NGD_SlotRef.slot_offset_loop.body := by
  delta {P}compact.slot_offset_loop.body NGD_SlotRef.slot_offset_loop.body
  simp only [PRVEq.NGD_SlotRef.Funs.SLOT_NODES]
#print axioms PRVEq.NGD_SlotRef.Funs.slot_offset_loop.body

theorem PRVEq.NGD_SlotRef.Funs.slot_offset_loop : @{P}compact.slot_offset_loop = @NGD_SlotRef.slot_offset_loop := by
  delta {P}compact.slot_offset_loop NGD_SlotRef.slot_offset_loop
  simp only [PRVEq.NGD_SlotRef.Funs.slot_offset_loop.body]
#print axioms PRVEq.NGD_SlotRef.Funs.slot_offset_loop

theorem PRVEq.NGD_SlotRef.Funs.slot_offset : @{P}compact.slot_offset = @NGD_SlotRef.slot_offset := by
  funext slot
  delta {P}compact.slot_offset NGD_SlotRef.slot_offset
  simp only [PRVEq.NGD_SlotRef.Funs.OFF_NODES, bind_tc_ok, PRVEq.NGD_SlotRef.Funs.slot_offset_loop]
#print axioms PRVEq.NGD_SlotRef.Funs.slot_offset
'''
# theorems are in namespace NGD_SlotRef; PRVEq names must be root: close namespace before them
open('PRVEq_NGD_SlotRef_Funs_s1.lean','w').write(out)
