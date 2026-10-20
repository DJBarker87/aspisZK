import FourDotsActualTermTraceRootV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow
namespace AspisR1FastDotsActualTermUniqueRootV1
open AspisR1FastDotsActualTermTraceRootV1
open AspisR1FastDotsActualTermInputTraceRootV1
abbrev U8 := Std.U8

/-- The actual checked offset/slice/copy path has one resulting byte array
for a fixed source buffer, slot and term. -/
theorem term_bytes_trace_unique
    (a : Array U8 608#usize) (slot term : Usize) (x y : Array U8 4#usize)
    (hx : TermBytesTrace a slot term x) (hy : TermBytesTrace a slot term y) : x=y := by
  rcases hx with ⟨o0,o1,o2,o3,o4,s,c,h0,h1,h2,h3,h4,hs,hc,hx⟩
  rcases hy with ⟨p0,p1,p2,p3,p4,t,d,k0,k1,k2,k3,k4,kt,kd,hy⟩
  have e0 : p0=o0 := Result.ok.inj (k0.symm.trans h0)
  have e1 : p1=o1 := Result.ok.inj (k1.symm.trans h1)
  subst p0; subst p1
  have e2 : p2=o2 := Result.ok.inj (k2.symm.trans h2)
  have e3 : p3=o3 := Result.ok.inj (k3.symm.trans h3)
  subst p2; subst p3
  have e4 : p4=o4 := Result.ok.inj (k4.symm.trans h4)
  subst p4
  have es : t=s := Result.ok.inj (kt.symm.trans hs)
  subst t
  have ec : d=c := Result.ok.inj (kd.symm.trans hc)
  subst d
  exact Result.ok.inj (hx.symm.trans hy)

/-- A retained source contribution's product is fixed by the source arrays,
slot and term, independently of which successful range trace exposes it. -/
theorem matched_term_product_unique
    (a : Array U8 608#usize) (a1 : Array Wide 29#usize) (slot : Usize)
    (iter1 next1 iter2 next2 : Range) (c d : Contribution)
    (hc : c.matches a a1 slot iter1 next1)
    (hd : d.matches a a1 slot iter2 next2) (hterm : c.term=d.term) :
    ∀ j : Fin 8, c.product j=d.product j := by
  rcases hc with ⟨hnextc,hbytesc,hparsec,hscalarc,hreadc,hcoeffc⟩
  rcases hd with ⟨hnextd,hbytesd,hparsed,hscalard,hreadd,hcoeffd⟩
  have hbytes : c.bytes=d.bytes := term_bytes_trace_unique a slot d.term c.bytes d.bytes
    (by simpa only [hterm] using hbytesc) hbytesd
  rw [hbytes] at hparsec
  have hscalar : c.scalar=d.scalar := Option.some.inj (Result.ok.inj (hparsec.symm.trans hparsed))
  rw [hterm] at hreadc
  have hwide : c.wide=d.wide := Result.ok.inj (hreadc.symm.trans hreadd)
  rw [hwide] at hcoeffc
  have hcoeff : c.coeff=d.coeff := Result.ok.inj (hcoeffc.symm.trans hcoeffd)
  intro j
  simp only [Contribution.product,hcoeff,hscalar]
#print axioms term_bytes_trace_unique
#print axioms matched_term_product_unique
end AspisR1FastDotsActualTermUniqueRootV1
