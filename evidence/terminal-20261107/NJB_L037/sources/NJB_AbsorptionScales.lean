import NJB_PreparedLaws
set_option autoImplicit false
noncomputable section
namespace AspisR1.NJB_AbsorptionScales
open Aeneas Aeneas.Std Result
open FIv_NativeArithmetic (NQ)
open FIv_NativeValue (Canon decode K)
open FIv_PreparedNew (NP)
structure Scale where
 value : NQ
 cache : NP
def model (low fixed two eight nodes : K) (i : Fin 3) : K :=
 match i.val with
 | 0 => low*fixed
 | 1 => low*(fixed+two)
 | _ => low*(fixed+two+eight+nodes)
/-- Source-ordered reviewed reference: repeated fixed+two is evaluated twice,
exactly as the frozen prologue, and each prepared cache has its own Result. -/
def reference (low fixed two eight nodes : NQ) : Result (Fin 3 → Scale) := do
 let q0 ← FIq_Native.field.QM31.mul low fixed
 let p0 ← FIq_Native.field.PreparedQm31Multiplier.new q0
 let t1 ← FIq_Native.field.QM31.add fixed two
 let q1 ← FIq_Native.field.QM31.mul low t1
 let p1 ← FIq_Native.field.PreparedQm31Multiplier.new q1
 let t2 ← FIq_Native.field.QM31.add fixed two
 let t3 ← FIq_Native.field.QM31.add t2 eight
 let t4 ← FIq_Native.field.QM31.add t3 nodes
 let q2 ← FIq_Native.field.QM31.mul low t4
 let p2 ← FIq_Native.field.PreparedQm31Multiplier.new q2
 ok ![⟨q0,p0⟩,⟨q1,p1⟩,⟨q2,p2⟩]
theorem result (low fixed two eight nodes : NQ)
 (hl : Canon low) (hf : Canon fixed) (ht : Canon two) (he : Canon eight) (hn : Canon nodes) :
 ∃ out,reference low fixed two eight nodes=ok out ∧
 ∀ i,Canon (out i).value ∧ NJB_PreparedLaws.Domain (out i).cache (out i).value ∧
 decode (out i).value=model (decode low) (decode fixed) (decode two) (decode eight) (decode nodes) i := by
 obtain ⟨q0,h0,c0,v0⟩ := NJB_StubLaws.qm_mul low fixed hl hf
 obtain ⟨p0,n0,d0⟩ := NJB_PreparedLaws.new_result q0 c0
 obtain ⟨t1,a1,ct1,vt1⟩ := NJB_StubLaws.qm_add fixed two hf ht
 obtain ⟨q1,h1,c1,v1⟩ := NJB_StubLaws.qm_mul low t1 hl ct1
 obtain ⟨p1,n1,d1⟩ := NJB_PreparedLaws.new_result q1 c1
 obtain ⟨t2,a2,ct2,vt2⟩ := NJB_StubLaws.qm_add fixed two hf ht
 obtain ⟨t3,a3,ct3,vt3⟩ := NJB_StubLaws.qm_add t2 eight ct2 he
 obtain ⟨t4,a4,ct4,vt4⟩ := NJB_StubLaws.qm_add t3 nodes ct3 hn
 obtain ⟨q2,h2,c2,v2⟩ := NJB_StubLaws.qm_mul low t4 hl ct4
 obtain ⟨p2,n2,d2⟩ := NJB_PreparedLaws.new_result q2 c2
 refine ⟨![⟨q0,p0⟩,⟨q1,p1⟩,⟨q2,p2⟩],?_,?_⟩
 · simp only [reference,h0,n0,a1,h1,n1,a2,a3,a4,h2,n2,bind_tc_ok]
 · intro i
   fin_cases i
   · exact ⟨c0,d0,v0⟩
   · refine ⟨c1,d1,?_⟩
     change decode q1=decode low*(decode fixed+decode two)
     rw [v1,vt1]
   · refine ⟨c2,d2,?_⟩
     change decode q2=decode low*(decode fixed+decode two+decode eight+decode nodes)
     rw [v2,vt4,vt3,vt2]
#print result
#print axioms result
end AspisR1.NJB_AbsorptionScales
end
