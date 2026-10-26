from pathlib import Path
import re,sys
root=Path(__file__).resolve().parents[2]
p=2147483647
for i in range(12):
 geo=(root/f'lean/JFs_TX2_Geo{10+i}.lean').read_text()
 lines=(root/f'lean/JFv_TX2_Line{10+i}.lean').read_text()
 x,y=map(int,re.search(r'def value0.*?⟨(\d+)#u32,(\d+)#u32',geo).groups())
 inp=re.findall(r'operations (\d+)#usize=ok value[012]',geo)
 lx,ly=[int(n) for n in re.findall(r'def value[12].*?:= (\d+)#u32',lines)]
 z=(2*lx*lx-1)%p
 mod=f'JFv_TX2_Row{10+i}'
 s=f'''import JFv_TX2_Line{10+i}
import JFv_TX2_NodeCall
import JFv_TX2_GeometryOps
import Port4C_GeometryGather
set_option autoImplicit false
noncomputable section
namespace AspisR1.{mod}
open Aeneas Aeneas.Std Result

def value : Port4C_GeometryGather.Row := ⟨{x}#u32,{y}#u32,{lx}#u32,{ly}#u32,{z}#u32⟩

theorem node : JFv_TX2_NodeCall.sourceCall value.lineX=ok value.lineZ := by
  obtain ⟨z,run,canon,hv⟩ := JFv_TX2_NodeCall.source value.lineX
  change z.val=(({lx}*{lx}%2147483647+{lx}*{lx}%2147483647)%2147483647+2147483647-1)%2147483647 at hv
  norm_num at hv
  have same : z=value.lineZ := UScalar.eq_of_val_eq hv
  exact same ▸ run

theorem source {{C : Type}} (err : C) (seed : Port3_NativeGeometryBody.Ops C) :
    (JFv_TX2_GeometryOps.install err seed).op15 {inp[0]}#usize=ok (⟨value.x,value.y⟩ : SAQ_Geometry.Point) ∧
    (JFv_TX2_GeometryOps.install err seed).op14 {inp[1]}#usize=ok value.lineX ∧
    (JFv_TX2_GeometryOps.install err seed).op14 {inp[2]}#usize=ok value.lineY ∧
    JFv_TX2_NodeCall.sourceCall value.lineX=ok value.lineZ := by
  refine ⟨?_,JFv_TX2_Line{10+i}.source1,JFv_TX2_Line{10+i}.source2,node⟩
  change (do let pt ← AspisR1QueryGeometryActual.fast_domain.fibre_point R17CurrentCM31Semantics.operations {inp[0]}#usize
             ok (⟨pt.x,pt.y⟩ : SAQ_Geometry.Point))=_
  rw [JFs_TX2_Geo{10+i}.source0,bind_tc_ok]
  rfl

theorem regular : ∀ a∈value.words,a.val<2147483647 ∧ a≠0#u32 := by
  intro a h
  simp only [value,Port4C_GeometryGather.Row.words,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with rfl|rfl|rfl|rfl|rfl <;> decide

#print axioms node
#print axioms source
#print axioms regular
end AspisR1.{mod}
end
'''
 dest=root/f'lean/{mod}.lean'
 if '--check' in sys.argv:assert dest.read_text()==s
 else:dest.write_text(s)
