import FourDotsActualTermByteContentsRootV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow
namespace AspisR1FastDotsActualTermByteOffsetsRootV1
open AspisR1FastDotsActualTermInputTraceRootV1
abbrev U8 := Std.U8

private theorem tryMk_success_value {ty : UScalarTy} (n : Nat) (x : UScalar ty)
    (h : UScalar.tryMk ty n = .ok x) : x.val=n := by
  by_cases hb : n < 2^ty.numBits
  · let z : UScalar ty := UScalar.ofNatCore n hb
    have hz : UScalar.tryMk ty n = .ok z := by
      simp [UScalar.tryMk,UScalar.tryMkOpt,UScalar.check_bounds,hb,Result.ofOption,z]
    have hx : x=z := Result.ok.inj (h.symm.trans hz)
    rw [hx]
    rfl
  · simp [UScalar.tryMk,UScalar.tryMkOpt,UScalar.check_bounds,hb,Result.ofOption] at h

private theorem checked_mul_value (a b out : Usize)
    (h : (a*b : Result Usize) = .ok out) : out.val=a.val*b.val := by
  change UScalar.tryMk UScalarTy.Usize (a.val*b.val) = .ok out at h
  exact tryMk_success_value _ out h

private theorem checked_add_value (a b out : Usize)
    (h : (a+b : Result Usize) = .ok out) : out.val=a.val+b.val := by
  change UScalar.tryMk UScalarTy.Usize (a.val+b.val) = .ok out at h
  exact tryMk_success_value _ out h

/-- The actual checked term-byte path reads exactly the four bytes beginning
at 120*slot+4*term in the original source buffer. No offset equation is a premise. -/
theorem actual_term_bytes_exact_offset
    (a : Array U8 608#usize) (slot term : Usize) (bytes : Array U8 4#usize)
    (htrace : TermBytesTrace a slot term bytes) :
    bytes.val = a.val.slice (slot.val*120+term.val*4) (slot.val*120+term.val*4+4) := by
  obtain ⟨o0,o1,o2,o3,o4,h0,h1,h2,h3,h4,hbytes⟩ :=
    AspisR1FastDotsActualTermByteContentsRootV1.actual_term_bytes_source_contents
      a slot term bytes htrace
  have v0 : o0.val=slot.val*120 := checked_mul_value slot 120#usize o0 h0
  have v1 : o1.val=term.val*4 := checked_mul_value term 4#usize o1 h1
  have v2 : o2.val=o0.val+o1.val := checked_add_value o0 o1 o2 h2
  have v3 : o3.val=o0.val+o1.val := checked_add_value o0 o1 o3 h3
  have v4 : o4.val=o3.val+4 := checked_add_value o3 4#usize o4 h4
  simpa only [v0,v1,v2,v3,v4] using hbytes
#print axioms actual_term_bytes_exact_offset
end AspisR1FastDotsActualTermByteOffsetsRootV1
