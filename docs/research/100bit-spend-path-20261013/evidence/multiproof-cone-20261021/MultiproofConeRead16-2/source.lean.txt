import MultiproofParserRef.Funs

set_option autoImplicit false
namespace AspisR1.MultiproofConeRead16
open Aeneas Aeneas.Std Result

/-- The owned fixed-field reader is total and reads exactly the first 16
original bytes. It neither allocates nor uses Formatter/unwrap. -/
theorem read16_total (bytes : Slice U8) (bound : 16 ≤ bytes.val.length) :
    ∃ chunk, MultiproofParserRef.reference.read16 bytes = ok chunk ∧
      chunk.val = bytes.val.take 16 := by
  generalize hxs : bytes.val = xs at bound
  cases xs with
  | nil => simp at bound
  | cons b0 xs =>
    cases xs with
    | nil => simp at bound
    | cons b1 xs =>
      cases xs with
      | nil => simp at bound
      | cons b2 xs =>
        cases xs with
        | nil => simp at bound
        | cons b3 xs =>
          cases xs with
          | nil => simp at bound
          | cons b4 xs =>
            cases xs with
            | nil => simp at bound
            | cons b5 xs =>
              cases xs with
              | nil => simp at bound
              | cons b6 xs =>
                cases xs with
                | nil => simp at bound
                | cons b7 xs =>
                  cases xs with
                  | nil => simp at bound
                  | cons b8 xs =>
                    cases xs with
                    | nil => simp at bound
                    | cons b9 xs =>
                      cases xs with
                      | nil => simp at bound
                      | cons b10 xs =>
                        cases xs with
                        | nil => simp at bound
                        | cons b11 xs =>
                          cases xs with
                          | nil => simp at bound
                          | cons b12 xs =>
                            cases xs with
                            | nil => simp at bound
                            | cons b13 xs =>
                              cases xs with
                              | nil => simp at bound
                              | cons b14 xs =>
                                cases xs with
                                | nil => simp at bound
                                | cons b15 xs =>
                                  simp only [MultiproofParserRef.reference.read16, Slice.index_usize,
                                    Slice.getElem?_Usize_eq, hxs]
                                  simp only [show (0#usize).val = 0 from rfl, show (1#usize).val = 1 from rfl, show (2#usize).val = 2 from rfl, show (3#usize).val = 3 from rfl, show (4#usize).val = 4 from rfl, show (5#usize).val = 5 from rfl, show (6#usize).val = 6 from rfl, show (7#usize).val = 7 from rfl, show (8#usize).val = 8 from rfl, show (9#usize).val = 9 from rfl, show (10#usize).val = 10 from rfl, show (11#usize).val = 11 from rfl, show (12#usize).val = 12 from rfl, show (13#usize).val = 13 from rfl, show (14#usize).val = 14 from rfl, show (15#usize).val = 15 from rfl,
                                    List.getElem?_cons_zero, List.getElem?_cons_succ, bind_tc_ok]
                                  exact ⟨_,rfl,rfl⟩

#print axioms read16_total
end AspisR1.MultiproofConeRead16
