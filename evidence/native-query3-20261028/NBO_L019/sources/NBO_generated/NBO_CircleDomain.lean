import NBO_GeometryDomain
import NBO_SquareCut
set_option autoImplicit false
noncomputable section
namespace NBO_CircleDomain
open Aeneas Aeneas.Std Result AspisR1 AspisR1Stage2 Port3_NativeQueryBody
open NBO_TailDomain (WideCanonical)
open NBO_QueryDomains (AllWide AllBase)
/-- Native little-endian word on the SAME byte carrier; salt and unconsumed
608..672 bytes are deliberately outside this field-domain predicate. -/
def word (q : Slice U8) (offset : Nat) : Nat :=
 (q.val[offset]?.getD 0#u8).val + 256*(q.val[offset+1]?.getD 0#u8).val +
 65536*(q.val[offset+2]?.getD 0#u8).val + 16777216*(q.val[offset+3]?.getD 0#u8).val
structure OpeningDomain (q : Slice U8) : Prop where
 length : q.val.length=832
 dots : ∀ j, j<152 → word q (4*j)<2147483647
 values : ∀ j, j<32 → word q (672+4*j)<2147483647
/-- Exact lower successful-domain statements for these two callee units.
No whole-query value/equality or successful final result is assumed. -/
structure Lower (ops : Ops) : Prop where
 dots : ∀ q g out, OpeningDomain q → AllWide g →
   ops.op20 q g=ok out → AllWide out
 circle : ∀ alpha dots inverse out, WideCanonical alpha → AllWide dots → AllBase inverse →
   ops.op17 alpha dots inverse=ok out → WideCanonical out
/-- SAME accepted query cuts derive all inputs and the return of the circle
fold. Caller scan/preparation domains are the exact named upstream obligations. -/
theorem reached (ops : Ops) (lower : Lower ops) (domains : NBO_QueryDomains.Lower ops)
 (proof : Slice U8) (p : verifier.Prepared) (a out : verifier.Accumulator)
 (g : Array Stage2E 29#usize) (goodG : AllWide g)
 (geometry : verifier.QueryGeometry) (goodGeometry : NBO_QueryDomains.GeometryDomain geometry)
 (b bout : verifier.BatchedWeights) (active : a.next.val<10)
 (alpha : WideCanonical (p.alpha.val[0]'(by rw [p.alpha.property];decide)))
 (opening : ∀ q, ops.op11 proof a.next=ok q → OpeningDomain q)
 (run : verifier.candidate.query_values (NBF_Accumulate.install ops)
   proof p a g none geometry b=ok (.Ok (out,bout))) :
 ∃ q dots inverse circle,
   ops.op11 proof a.next=ok q ∧ ops.op20 q g=ok dots ∧
   ops.op18 geometry a.next=ok inverse ∧
   ops.op17 (p.alpha.val[0]'(by rw [p.alpha.property];decide)) dots inverse=ok circle ∧
   OpeningDomain q ∧ AllWide dots ∧ AllBase inverse ∧ WideCanonical circle := by
 obtain ⟨query,q,dots,inverse,circle,values,line,node,hquery,hq,hdots,hinverse,hcircle,hline,haccum⟩ :=
   NBF_QueryCuts.accepted (NBF_Accumulate.install ops) proof p a out g none geometry b bout run
 have qDomain : OpeningDomain q := opening q hq
 have dotsDomain : AllWide dots := lower.dots q g dots qDomain goodG hdots
 have invDomain : AllBase inverse := domains.inverse geometry a.next inverse goodGeometry active hinverse
 exact ⟨q,dots,inverse,circle,hq,hdots,hinverse,hcircle,qDomain,dotsDomain,invDomain,
   lower.circle _ dots inverse circle alpha dotsDomain invDomain hcircle⟩
#print axioms reached
end NBO_CircleDomain
end
