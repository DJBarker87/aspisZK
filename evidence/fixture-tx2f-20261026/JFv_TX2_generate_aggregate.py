from pathlib import Path
import re,sys
root=Path(__file__).resolve().parents[2]
qs=[]
for i in range(12):
 s=(root/f'lean/JFs_TX2_Geo{10+i}.lean').read_text();qs.append(int(re.search(r'operations (\d+)#usize=ok value0',s)[1]))
s=''.join(f'import JFv_TX2_Row{i}\n' for i in range(10,22))+'''import JFs_TX2_GeometryPoints
import JFv_TX2_DecodeNonzero
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFv_TX2_Rows
open Aeneas Aeneas.Std Result
abbrev input := JFs_TX2_GeometryPoints.input
'''
for name,typ,vals in [('value','Port4C_GeometryGather.Row',[f'JFv_TX2_Row{10+i}.value' for i in range(12)]),('query','U32',[f'{u}#u32' for u in qs]),('parent','Usize',[f'{u//4}#usize' for u in qs])]:
 s+=f'def {name} (i : Fin 12) : {typ} := match i.val with\n'
 for i,v in enumerate(vals):s+=f'  | {i if i<11 else "_"} => {v}\n'
s+='''
theorem source {C : Type} (err : C) (seed : Port3_NativeGeometryBody.Ops C) (i : Fin 12) :
    (JFv_TX2_GeometryOps.install err seed).op15 (input i 0)=ok (⟨(value i).x,(value i).y⟩ : SAQ_Geometry.Point) ∧
    (JFv_TX2_GeometryOps.install err seed).op14 (input i 1)=ok (value i).lineX ∧
    (JFv_TX2_GeometryOps.install err seed).op14 (input i 2)=ok (value i).lineY ∧
    JFv_TX2_NodeCall.sourceCall (value i).lineX=ok (value i).lineZ := by
  fin_cases i
'''+''.join(f'  · exact JFv_TX2_Row{10+i}.source err seed\n' for i in range(12))
s+='''
theorem regular (i : Fin 12) : ∀ a∈(value i).words,a.val<2147483647 ∧ a≠0#u32 := by
  fin_cases i
'''+''.join(f'  · exact JFv_TX2_Row{10+i}.regular\n' for i in range(12))
s+='''
theorem nonzero (i : Fin 12) : ∀ a∈(value i).words,S7JoinBasisMachine.decode a≠0 := by
  intro a ha
  obtain ⟨hc,hn⟩ := regular i a ha
  exact JFv_TX2_DecodeNonzero.source a hc hn

'''
s+=(Path(__file__).resolve().parent/'JFv_TX2_addresses.txt').read_text()
s+='''theorem fibres {C : Type} (err : C) (seed : Port3_NativeGeometryBody.Ops C)
    (i : Fin 12) (k : Fin 3) :
    (JFv_TX2_GeometryOps.install err seed).op12 (input i k)=ok (.Ok (input i k)) := by
  change SAQ_Constructor.fibre err (input i k)=_
  have bound : input i k<262144#usize := by fin_cases i <;> fin_cases k <;> decide
  simp only [SAQ_Constructor.fibre,if_pos bound]

#print axioms source
#print axioms regular
#print axioms nonzero
#print axioms addresses
#print axioms fibres
end AspisR1.JFv_TX2_Rows
end
'''
p=Path(__file__).resolve().parent/'JFv_TX2_Rows_UNCHECKED.lean.txt'
if '--check' in sys.argv:assert p.read_text()==s
else:p.write_text(s)
