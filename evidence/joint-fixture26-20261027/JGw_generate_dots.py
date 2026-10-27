from pathlib import Path
import sys
P=Path(__file__).resolve().parent;R=P.parents[1]
for i in range(10):
 ns=f'JGw_Dots{i}'
 s=f'''import JGw_Scalars{i}
import JGw_Tails{i:02}
import JGw_DotTotal
import JFs_TX2_FourHead
import FIp_DotsAllCanonical
import FIp_DotsOutputCanonical
set_option autoImplicit false
noncomputable section
namespace AspisR1.{ns}
open Aeneas Aeneas.Std Result

def q : Array U8 608#usize := JFr_TX2_Windows.array ⟨{i},by decide⟩
def scalar (slot : Fin 4) (term : Fin 26) : U32 := match slot.val with
'''
 for j in range(4):s+=f"  | {'_' if j==3 else j} => JGw_Slot{i:02}_{j}.values.val[term.val]'(by rw [JGw_Slot{i:02}_{j}.values.property];exact term.isLt)\n"
 s+='''
theorem reads (slot : Fin 4) (term : Fin 26) :
    JFr_TX2_ScalarRead.read q (Usize.ofNat slot.val (by have:=slot.isLt;scalar_tac))
      (JFr_TX2_DotTerm.cursor term.val (by have:=term.isLt;omega))=ok (scalar slot term) := by
  fin_cases slot
'''
 for j in range(4):s+=f'  · exact JGw_Slot{i:02}_{j}.source term\n'
 s+='''#print axioms reads

theorem canonical (slot : Fin 4) (term : Fin 26) : (scalar slot term).val<2147483647 := by
  fin_cases slot
'''
 for j in range(4):s+=f'  · exact JFr_TX2_ScalarCanon.source _ _ (JGw_Slot{i:02}_{j}.decode term)\n'
 s+='#print axioms canonical\n'
 for k in range(3):
  s+=f'''
theorem tail{k} (slot : Fin 4) :
    ∃ v, JFr_TX2_TailRead.read q (JFr_TX2_Tails.offset slot {k}) (JFr_TX2_Tails.stop slot {k})=ok v := by
  fin_cases slot
'''
  for j in range(4):s+=f'  · exact ⟨_,JGw_Tails{i:02}.source{k}_{j}⟩\n'
  s+=f'#print axioms tail{k}\n'
 s+='''
theorem slot (j : Fin 4) :
    ∃ out, FIp_NativeDots.fast_dots.four_dots_one q JFr_TX2_FirstLane.native
      (Usize.ofNat j.val (by have:=j.isLt;scalar_tac))=ok out ∧ FIo_WideValues.Canon out := by
  obtain ⟨q0,h0⟩ := tail0 j
  obtain ⟨q1,h1⟩ := tail1 j
  obtain ⟨q2,h2⟩ := tail2 j
  exact JGw_DotTotal.source q j (scalar j) (reads j) (canonical j) q0 q1 q2 h0 h1 h2
#print axioms slot

theorem native :
    ∃ out, FIp_NativeDots.fast_dots.four_dots (JFo_Opening.value ⟨'''+str(i)+''',by decide⟩)
      JFr_TX2_FirstLane.native=ok out ∧ FIo_ArrayCanon.Holds out := by
'''
 for j,name in enumerate('abcd'):
  s+=f'  obtain ⟨{name},h{j},_⟩ := slot {j}\n'
  s+=f'  have z{j} : Usize.ofNat (({j}:Fin 4).val) (by have:=({j}:Fin 4).isLt;scalar_tac)={j}#usize := by\n    apply UScalar.eq_of_val_eq\n    rfl\n  rw [z{j}] at h{j}\n'
 s+='''  let out : Array FIo_Install.NE 4#usize := Array.make 4#usize [a,b,c,d]
  have run : FIp_NativeDots.fast_dots.four_dots (JFo_Opening.value ⟨'''+str(i)+''',by decide⟩)
      JFr_TX2_FirstLane.native=ok out := by
    rw [JFs_TX2_FourHead.source]
    change JFs_TX2_FourHead.slots q JFr_TX2_FirstLane.native=ok out
    simp only [JFs_TX2_FourHead.slots,h0,h1,h2,h3,bind_tc_ok]
    rfl
  exact ⟨out,run,FIp_DotsAllCanonical.four _ _ out run⟩
#print axioms native

def value : Array FIp_DotsAdapter.E 4#usize := FIp_DotsAdapter.fromArray (Classical.choose native)

theorem source : FIp_DotsAdapter.dots (JFo_Opening.value ⟨'''+str(i)+''',by decide⟩)
    JFr_TX2_Powers.value=ok value := by
  change (do let out ← FIp_NativeDots.fast_dots.four_dots
               (JFo_Opening.value ⟨'''+str(i)+''',by decide⟩) JFr_TX2_FirstLane.native
             ok (FIp_DotsAdapter.fromArray out))=ok value
  rw [(Classical.choose_spec native).1,bind_tc_ok]
  rfl
#print axioms source

theorem output_canonical : ∀ x∈value.val, Port4C_QueryArithmetic.CanonE x :=
  FIp_DotsOutputCanonical.all _ _ _ source
#print axioms output_canonical
'''
 s+=f'end AspisR1.{ns}\nend\n'
 f=R/f'lean/{ns}.lean'
 if '--check' in sys.argv:assert f.read_text()==s,f
 else:f.write_text(s)
print('checked' if '--check' in sys.argv else 'generated', 'ten actual native TX1 dot source modules')
