import NKK_NativeRaw
set_option autoImplicit false
noncomputable section
namespace NKK_NativeRaw
open Aeneas Aeneas.Std Result AspisR1 NID_ResumeEmission

theorem read_chain (n : Usize) (count : Nat) (r : Reader)
 (bound : r.at.val+n.val*count≤r.bytes.val.length) :
 ∃ bs last, Chain n r bs last ∧ bs.length=count ∧ reads n count r=ok (bs,last) := by
 induction count generalizing r with
 | zero => exact ⟨[],r,.nil r,rfl,rfl⟩
 | succ count ih =>
  obtain ⟨b,next,step,call⟩ := one n r (by rw [Nat.mul_succ] at bound;omega)
  have nextBound : next.at.val+n.val*count≤next.bytes.val.length := by
   have cursor := step.2.1
   have backing := step.2.2
   rw [backing]
   rw [Nat.mul_succ] at bound
   omega
  obtain ⟨bs,last,chain,size,tail⟩ := ih next nextBound
  refine ⟨b::bs,last,.cons step chain,by simp only [List.length_cons,size],?_⟩
  rw [reads,call]
  change (do let (bs,last) ← reads n count next;ok (b::bs,last))=_
  rw [tail]
  rfl

theorem read_result {n : Usize} {r last : Reader} {bs : List (Array U8 n)}
 (chain : Chain n r bs last) :
 (r.at.val+n.val*bs.length≤r.bytes.val.length) → reads n bs.length r=ok (bs,last) := by
 induction chain with
 | nil r => intro bound;rfl
 | @cons r next last b bs step tail ih =>
  intro bound
  have firstBound : r.at.val+n.val≤r.bytes.val.length := by
   simp only [List.length_cons,Nat.mul_succ] at bound
   omega
  obtain ⟨actual,out,cut,call⟩ := one n r firstBound
  have cutSame : actual=b ∧ out=next := by
   have bytes : actual=b := Subtype.ext (cut.1.trans step.1.symm)
   have cursor : out.at=next.at := UScalar.eq_of_val_eq (cut.2.1.trans step.2.1.symm)
   have backing : out.bytes=next.bytes := cut.2.2.trans step.2.2.symm
   cases out;cases next;simp_all
  have actualCall : NJC_ConcreteUnwrap.raw n r=ok (b,next) := by
   simpa only [cutSame.1,cutSame.2] using call
  have nextBound : next.at.val+n.val*bs.length≤next.bytes.val.length := by
   rw [step.2.2]
   have advance:=step.2.1
   simp only [List.length_cons,Nat.mul_succ] at bound
   omega
  simp only [List.length_cons]
  rw [reads,actualCall]
  change (do let (bs,last) ← reads n bs.length next;ok (b::bs,last))=_
  rw [ih nextBound]
  rfl

#print axioms read_chain
#print axioms read_result
end NKK_NativeRaw
