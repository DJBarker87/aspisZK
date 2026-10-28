import NCE_OpeningCuts

set_option autoImplicit false
namespace AspisR1.NCM_OpeningShape
open Aeneas Aeneas.Std Result NCE_OpeningCuts

/-- The logical reader image has the requested width whenever it returns.
This lemma makes no native claim and requires no reader correctness premise. -/
theorem length (reader : Reader) (i width offset : Nat) (s : Carrier)
    (bytes : List U8) (after : Carrier)
    (returned : readWindow reader i width offset s = ok (bytes,after)) : bytes.length = width := by
  induction width generalizing offset s bytes after with
  | zero =>
    have same := Result.ok.inj returned
    cases same
    rfl
  | succ width ih =>
    simp only [readWindow] at returned
    cases first : reader s (10055+832*i+offset) with
    | fail e => simp only [first,bind_tc_fail] at returned;cases returned
    | div => simp only [first,bind_tc_div] at returned;cases returned
    | ok got =>
      simp only [first,bind_tc_ok] at returned
      cases rest : readWindow reader i width (offset+1) got.2 with
      | fail e => simp only [rest,bind_tc_fail] at returned;cases returned
      | div => simp only [rest,bind_tc_div] at returned;cases returned
      | ok tail =>
        simp only [rest,bind_tc_ok] at returned
        cases Result.ok.inj returned
        simp only [List.length_cons,ih (offset+1) got.2 tail.1 tail.2 rest]

#print axioms length
end AspisR1.NCM_OpeningShape
