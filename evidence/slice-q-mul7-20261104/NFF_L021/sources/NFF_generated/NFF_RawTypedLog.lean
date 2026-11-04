import NFF_RawLog
set_option autoImplicit false
noncomputable section
namespace AspisR1.NFF_RawTypedLog
open Aeneas Aeneas.Std Result
abbrev Q := NFE_NFC_RawValues.Q

def words (x : Q) : NFF_RawLog.Words := fun i => x.val[i.val]!.val

theorem canonical (x : Q) (hx : NFE_NFC_RawValues.Canon x) :
    ∀ i,words x i<NEG_DotDomain.P := by
  intro i
  fin_cases i <;> simp_all [words,NFE_NFC_RawValues.Canon,NEG_DotDomain.P] <;> omega

theorem operands (x y : Q) (hx : NFE_NFC_RawValues.Canon x)
    (hy : NFE_NFC_RawValues.Canon y) :
    ∀ i,(NFF_RawLog.operands (words x) (words y) i).1<NEG_DotDomain.P ∧
      (NFF_RawLog.operands (words x) (words y) i).2<NEG_DotDomain.P := by
  intro i
  have a:=canonical x hx
  have b:=canonical y hy
  unfold NFF_RawLog.operands
  split <;> exact ⟨a _,b _⟩

/-- The log's natural value identifies the actual emitted raw call. Its
products are constrained individually on caller-derived canonical operands. -/
theorem replay (x y : Q) (hx : NFE_NFC_RawValues.Canon x)
    (hy : NFE_NFC_RawValues.Canon y) (p : NFF_RawLog.Log)
    (law : ∀ i,NEG_ProductAbstraction.Product 64
      (NFF_RawLog.operands (words x) (words y) i).1
      (NFF_RawLog.operands (words x) (words y) i).2 (p i)) :
    ∃ a b c d : U64,
      FIo_Native.fast_pairing.canonical.Q.raw x y=ok (Array.make 4#usize [a,b,c,d]) ∧
      (a.val,b.val,c.val,d.val)=NFF_RawLog.evaluate p := by
  obtain ⟨a,b,c,d,run,value⟩:=NFE_NFC_RawValues.source x y hx hy
  have logged:=NFF_RawLog.replay (words x) (words y) p (operands x y hx hy) law
  have same : NFE_NFC_RawValues.spec x y=NFF_RawLog.evaluate p := by
    rw [logged]
    rfl
  exact ⟨a,b,c,d,run,value.trans same⟩

#print axioms canonical
#print axioms operands
#print axioms replay
end AspisR1.NFF_RawTypedLog
end
