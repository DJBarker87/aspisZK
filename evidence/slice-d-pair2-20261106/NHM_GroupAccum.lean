import NHI_Scalar
import NHM_GroupWeightDomain
set_option autoImplicit false
namespace NHM_GroupAccum
open Aeneas Aeneas.Std Result ControlFlow AspisR1 LPi_FieldValues
abbrev Cells := NHM_GroupCoefficient.Cells
abbrev State := NHM_GroupWeight.State

def window (cells : Cells) (group : Usize) (weight pair : NE) : Result NE := do
 let coefficient ← Array.index_usize cells group
 let product ← FIo_Native.aspis_core.field.wide_exact.WideExact.mul coefficient weight
 FIo_Native.aspis_core.field.wide_exact.WideExact.add pair product

def body (low : Array NE 16#usize) (cells : Cells) (s : State) : Result (ControlFlow State NE) := do
 let (o,next) ← core.iter.range.IteratorRange.next core.iter.range.StepUsize s.1
 match o with
 | none=>ok (.done s.2)
 | some group=>do
  let weight ← NHM_GroupWeight.reference low group NHI_Scalar.zero
  let out ← window cells group weight s.2
  ok (.cont (next,out))

theorem step (low : Array NE 16#usize) (cells : Cells) (s : State) :
 FIo_Native.weights.s2_grouped_inactive_pair_loop1.body low cells s.1 s.2=body low cells s := by
 unfold FIo_Native.weights.s2_grouped_inactive_pair_loop1.body body window
 simp only [NHM_GroupWeight.source,bind_assoc_eq,bind_tc_ok]
 rfl

theorem canonical (cells : Cells) (hc : ∀ x∈cells.val,canonE x) (group : Usize)
 (weight pair out : NE) (hw : canonE weight) (hp : canonE pair)
 (run : window cells group weight pair=ok out) : canonE out := by
 unfold window at run
 obtain ⟨coefficient,hr,run⟩ := Port3_PushFrame.bind_success _ _ _ run
 obtain ⟨product,hm,run⟩ := Port3_PushFrame.bind_success _ _ _ run
 have cc:=NHM_ArrayCanon.read canonE cells group coefficient hc hr
 obtain ⟨product',hm',cm,_⟩ := LPi_TowerValues.wide_mul coefficient weight cc hw
 have same:=Result.ok.inj (hm'.symm.trans hm)
 subst product'
 obtain ⟨out',ho,co⟩ := NGW_PolynomialAdd.total pair product hp cm
 have same:=Result.ok.inj (ho.symm.trans run)
 subst out'
 exact co

theorem progress (low : Array NE 16#usize) (cells : Cells) (s t : State)
 (run : body low cells s=ok (.cont t)) :
 t.1.end=s.1.end ∧ t.1.start.val=s.1.start.val+1 ∧ s.1.start.val<s.1.end.val := by
 unfold body at run
 obtain ⟨⟨o,next⟩,hn,run⟩ := Port3_PushFrame.bind_success _ _ _ run
 cases o with
 | none=>cases run
 | some group=>
  obtain ⟨weight,hw,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨out,ho,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  have same:=ControlFlow.cont.inj (Result.ok.inj run)
  rw [←same]
  exact (NHI_RangeProgress.some_next s.1 next group hn).2

theorem decreases (low : Array NE 16#usize) (cells : Cells) (s t : State)
 (run : body low cells s=ok (.cont t)) :
 t.1.end.val-t.1.start.val<s.1.end.val-s.1.start.val := by
 obtain ⟨last,inc,more⟩ := progress low cells s t run
 have value:=congrArg (fun x : Usize=>x.val) last
 omega

def reference (low : Array NE 16#usize) (cells : Cells) (pair : NE) :=
 NHI_CountedLoop.unroll (body low cells) 13 ({start:=0#usize,«end»:=12#usize},pair)

theorem source (low : Array NE 16#usize) (cells : Cells) (pair : NE) :
 FIo_Native.weights.s2_grouped_inactive_pair_loop1
  {start:=0#usize,«end»:=12#usize} low cells pair=reference low cells pair := by
 unfold FIo_Native.weights.s2_grouped_inactive_pair_loop1 reference
 have same : (fun s : State=>FIo_Native.weights.s2_grouped_inactive_pair_loop1.body low cells s.1 s.2)=body low cells := funext (step low cells)
 rw [same]
 exact NHI_CountedLoop.agrees (body low cells) (fun s=>s.1.end.val-s.1.start.val)
  (decreases low cells) 13 _ (by change (12:Nat)-0<13;omega)

#print axioms step
#print axioms canonical
#print axioms progress
#print axioms decreases
#print axioms source
end NHM_GroupAccum
