import NKI_ValueTraceFactor
import NKI_ArrayFrame
import NIH_SelectorRow
set_option autoImplicit false
noncomputable section
namespace AspisR1.NKI_ValueFields
open Aeneas Aeneas.Std Result FIq_Native
open FIv_NativeValue (decode)
open NKI_ValuePrefix (Openings Selectors)
open NKI_ValueTrace (Locals)
def row (g : Fin 3) : Usize := UScalar.ofNatCore (1008+2*g.val) (by have h:=g.isLt;scalar_tac)
theorem row_value (g : Fin 3) : (row g).val=1008+2*g.val := rfl

theorem rows (o : Openings) (s : Selectors) (l : Locals)
 (calls : NKI_ValueTrace.Clauses o s l) (hh : FIw_ArrayValue.canonical s.high) (hl : FIw_ArrayValue.canonical s.low) :
 ∀ g : Fin 3,pool_v1.pair_forest_copy_terminal.Selectors.row s (row g)=ok (NJB_ArrayCarrier.cell l.value_selectors g) := by
 have mapCall:=calls.1
 have v:=FIy_ValueSelector.value s l.value_selectors hh hl mapCall
 intro g
 obtain ⟨q,cq,hq,vq⟩ := NIH_SelectorRow.result s (row g) (by rw [row_value];have h:=g.isLt;omega) hh hl
 have eq : q=NJB_ArrayCarrier.cell l.value_selectors g := by
  apply NJB_DecodeInjective.qm _ _ hq (NJB_ArrayCarrier.canonical_cell _ v.1 g)
  change decode q=FIw_ArrayValue.decoded l.value_selectors g
  rw [v.2]
  simp only [FIy_ValueSelector.model,FIy_FrontierMeaning.rowValue]
  rw [row_value] at vq
  exact vq
 simpa only [eq] using cq

def Reads (o : Openings) (l : Locals) : Prop :=
 l.q=NJB_ArrayCarrier.cell l.value_selectors 0 ∧ l.q2=NJB_ArrayCarrier.cell l.value_selectors 1 ∧ l.q4=NJB_ArrayCarrier.cell l.value_selectors 2 ∧
 l.q11=NJB_ArrayCarrier.cell o.z 10 ∧ l.q13=NJB_ArrayCarrier.cell o.succ_z 10 ∧ l.q14=NJB_ArrayCarrier.cell o.xor12_z 10

theorem reads (o : Openings) (s : Selectors) (l : Locals) (calls : NKI_ValueTrace.Clauses o s l) (hc : NKI_ValueTrace.Canonical o l) : Reads o l := by
 have o3 : l.openings3=o := hc.2.2.2.2.2.2.2.2.2.2.2.1
 refine ⟨?_,?_,?_,?_,?_,?_⟩
 · have c:=calls.2.1
   exact NKI_ArrayFrame.read l.value_selectors 0#usize 0 l.q rfl c
 · have c:=calls.2.2.2.1
   exact NKI_ArrayFrame.read l.value_selectors 1#usize 1 l.q2 rfl c
 · have c:=calls.2.2.2.2.2.1
   exact NKI_ArrayFrame.read l.value_selectors 2#usize 2 l.q4 rfl c
 · have c:=calls.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
   rw [o3] at c
   exact NKI_ArrayFrame.read o.z 10#usize 10 l.q11 rfl c
 · have c:=calls.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
   rw [o3] at c
   exact NKI_ArrayFrame.read o.succ_z 10#usize 10 l.q13 rfl c
 · have c:=calls.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
   rw [o3] at c
   exact NKI_ArrayFrame.read o.xor12_z 10#usize 10 l.q14 rfl c
theorem loops (o : Openings) (s : Selectors) (l : Locals) (calls : NKI_ValueTrace.Clauses o s l) (hc : NKI_ValueTrace.Canonical o l) :
 FIx_ValueBitPrefix.calls o (Array.repeat 33#usize field.QM31.ZERO)=ok (o,l.range3) := by
 have o1 : l.openings1=o := hc.2.2.2.2.2.2.2.1
 have o2 : l.openings2=o := hc.2.2.2.2.2.2.2.2.2.1
 have o3 : l.openings3=o := hc.2.2.2.2.2.2.2.2.2.2.2.1
 have c0:=calls.2.2.2.2.2.2.2.1
 have c1:=calls.2.2.2.2.2.2.2.2.1
 have c2:=calls.2.2.2.2.2.2.2.2.2.1
 rw [o1] at c0 c1
 rw [o2] at c1 c2
 rw [o3] at c2
 unfold FIx_ValueBitPrefix.calls
 rw [c0,bind_tc_ok]
 change (do let (o2,r2)←pool_v1.pair_forest_semantic_terminal.add_value_lanes_loop1 o l.range1 0#usize
            pool_v1.pair_forest_semantic_terminal.add_value_lanes_loop2 o2 r2 0#usize)=ok (o,l.range3)
 rw [c1,bind_tc_ok]
 exact c2
#print axioms row_value
#print axioms rows
#print axioms reads
#print axioms loops
end AspisR1.NKI_ValueFields
end
