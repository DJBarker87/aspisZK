import NFF_RawLog
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace AspisR1.NFF_RawPacket
open Aeneas Aeneas.Std Result
abbrev Q := NFE_NFC_RawValues.Q

def words (x : Q) : NFF_RawLog.Words := fun i => x.val[i.val]!.val

theorem domains (x y : Q) (hx : NFE_NFC_RawValues.Canon x)
    (hy : NFE_NFC_RawValues.Canon y) : ∀ i,
    (NFF_RawLog.operands (words x) (words y) i).1<NEG_DotDomain.P ∧
    (NFF_RawLog.operands (words x) (words y) i).2<NEG_DotDomain.P := by
  intro i
  rcases hx with ⟨a,b,c,d⟩
  rcases hy with ⟨e,f,g,h⟩
  fin_cases i <;> simp only [NFF_RawLog.operands,words] <;>
    unfold NEG_DotDomain.P <;> constructor <;> omega

/-- The SAME product log yields the actual adopted raw call's four values.
This supplies no freely selected whole-callee reply. -/
theorem replay (x y : Q) (hx : NFE_NFC_RawValues.Canon x)
    (hy : NFE_NFC_RawValues.Canon y) (p : NFF_RawLog.Log)
    (law : ∀ i,NEG_ProductAbstraction.Product 64
      (NFF_RawLog.operands (words x) (words y) i).1
      (NFF_RawLog.operands (words x) (words y) i).2 (p i)) :
    ∃ r0 r1 r2 r3 : U64,
      FIo_Native.fast_pairing.canonical.Q.raw x y=ok (Array.make 4#usize [r0,r1,r2,r3]) ∧
      (r0.val,r1.val,r2.val,r3.val)=NFF_RawLog.evaluate p := by
  obtain ⟨r0,r1,r2,r3,run,value⟩:=NFE_NFC_RawValues.source x y hx hy
  have log:=NFF_RawLog.replay (words x) (words y) p (domains x y hx hy) law
  have same : NFE_NFC_RawValues.spec x y=
      R22RawQmProductResidues.rawCoefficients
        (words x 0) (words x 1) (words x 2) (words x 3)
        (words y 0) (words y 1) (words y 2) (words y 3) := rfl
  exact ⟨r0,r1,r2,r3,run,value.trans (same.trans log.symm)⟩

#print axioms domains
#print axioms replay
end AspisR1.NFF_RawPacket
