import NHX_FactoredTail
set_option autoImplicit false
namespace NHX_FactoredCut
open Aeneas Aeneas.Std Result ControlFlow AspisR1 LPi_FieldValues
open NHM_FactoredPrefix

def prefix_run (ap0 ap1 : Cells) (low high : Array NQ 4#usize) : Result (NE×NE×NE×NE) := do
 let scalar ← FIo_Native.weights.Weights.scalar_factor low ap0
 let t0 ← NHM_FactoredTerm.term ap1 high 0#usize
 let t1 ← NHM_FactoredTerm.term ap1 high 1#usize
 let t2 ← NHM_FactoredTerm.term ap1 high 2#usize
 let t3 ← NHM_FactoredTerm.term ap1 high 3#usize
 let (first2,first3,all) ← NHM_FactoredSums.run t0 t1 t2 t3
 ok (scalar,first2,first3,all)

def suffix (ap1 : Cells) (side : Usize) (iter : Iter) (weights : Cells)
 (q4 q16 : NQ) (p : NE×NE×NE×NE) : Result (ControlFlow State Cells) := do
 let (low,first2,first3,all):=p
 if side=0#usize then
  let x ← FIo_Native.aspis_core.field.wide_exact.WideExact.mul low all
  let w ← Array.update weights 0#usize x
  let y ← FIo_Native.aspis_core.field.wide_exact.WideExact.mul low first3
  let z ← FIo_Native.aspis_core.field.wide_exact.WideExact.mul_qm31 y q16
  let w1 ← Array.update w 1#usize z
  ok (.cont (iter,w1))
 else
  let old ← Array.index_usize weights 1#usize
  let a := NHI_ScalarDomain.pick ap1 1 (by decide)
  let quarter ← FIo_Native.aspis_core.field.wide_exact.WideExact.mul_m31 a FIo_Native.weights.QUARTER
  let product ← FIo_Native.aspis_core.field.wide_exact.WideExact.mul low quarter
  let x ← FIo_Native.aspis_core.field.wide_exact.WideExact.add old product
  let w ← Array.update weights 1#usize x
  let y ← FIo_Native.aspis_core.field.wide_exact.WideExact.mul low all
  let z ← FIo_Native.aspis_core.field.wide_exact.WideExact.mul_qm31 y q4
  let w1 ← Array.update w 2#usize z
  let a1 ← FIo_Native.aspis_core.field.wide_exact.WideExact.mul low first2
  let b ← FIo_Native.aspis_core.field.QM31.mul q16 q4
  let c ← FIo_Native.aspis_core.field.wide_exact.WideExact.mul_qm31 a1 b
  let w2 ← Array.update w1 3#usize c
  ok (.cont (iter,w2))

theorem prefix_total (ap0 ap1 : Cells) (low high : Array NQ 4#usize)
 (ha : ∀ x∈ap0.val,canonE x) (hb : ∀ x∈ap1.val,canonE x)
 (hl : ∀ x∈low.val,canonQ x) (hh : ∀ x∈high.val,canonQ x) :
 ∃ a b c d,prefix_run ap0 ap1 low high=ok (a,b,c,d) ∧ canonE a ∧ canonE b ∧ canonE c ∧ canonE d := by
 obtain ⟨s,a,hs,cs,ha0,ca,hv⟩:=NHI_Scalar.total low ap0 ha hl
 obtain ⟨t0,h0,c0⟩:=NHM_FactoredTerm.total ap1 high hb hh 0#usize (by decide)
 obtain ⟨t1,h1,c1⟩:=NHM_FactoredTerm.total ap1 high hb hh 1#usize (by decide)
 obtain ⟨t2,h2,c2⟩:=NHM_FactoredTerm.total ap1 high hb hh 2#usize (by decide)
 obtain ⟨t3,h3,c3⟩:=NHM_FactoredTerm.total ap1 high hb hh 3#usize (by decide)
 obtain ⟨b,c,d,hr,cb,cc,cd⟩:=NHM_FactoredSums.total t0 t1 t2 t3 c0 c1 c2 c3
 exact ⟨a,b,c,d,by simp only [prefix_run,ha0,h0,h1,h2,h3,hr,bind_tc_ok];rfl,ca,cb,cc,cd⟩

/-- Exact same emitted prefix_run; only fixed four-entry array reads are reduced. -/
theorem split (ap0 ap1 : Cells) (side : Usize) (iter : Iter) (weights : Cells)
 (low high : Array NQ 4#usize) (q4 q16 : NQ) :
 tail ap0 ap1 side iter weights low high q4 q16=
 (do let p ← prefix_run ap0 ap1 low high;suffix ap1 side iter weights q4 q16 p) := by
 have a1:=NHI_ScalarDomain.index ap1 1#usize (by decide)
 have p0 : Array.index_usize FIo_Native.weights.PERM 0#usize=ok 0#usize:=by simp only [FIo_Native.weights.PERM];rfl
 have p1 : Array.index_usize FIo_Native.weights.PERM 1#usize=ok 3#usize:=by simp only [FIo_Native.weights.PERM];rfl
 have p2 : Array.index_usize FIo_Native.weights.PERM 2#usize=ok 2#usize:=by simp only [FIo_Native.weights.PERM];rfl
 have p3 : Array.index_usize FIo_Native.weights.PERM 3#usize=ok 1#usize:=by simp only [FIo_Native.weights.PERM];rfl
 simp only [tail,prefix_run,suffix,NHM_FactoredTerm.term,NHM_FactoredSums.run,
  bind_assoc_eq,bind_tc_ok,p0,p1,p2,p3,NHX_FactoredTail.get0,NHX_FactoredTail.get1,
  NHX_FactoredTail.get2,NHX_FactoredTail.get3,a1]
 rfl

#print axioms prefix_total
#print axioms split
end NHX_FactoredCut
