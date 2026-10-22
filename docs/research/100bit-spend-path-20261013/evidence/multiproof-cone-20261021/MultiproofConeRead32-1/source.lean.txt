import MultiproofConeRef.Funs

set_option autoImplicit false
namespace AspisR1.MultiproofConeRead32
open Aeneas Aeneas.Std Result

/-- The owned fixed-field reader is total and reads exactly the first 32
original bytes. It neither allocates nor uses Formatter/unwrap. -/
theorem read32_total (bytes : Slice U8) (bound : 32 ≤ bytes.val.length) :
    ∃ chunk, MultiproofConeRef.reference.read32 bytes = ok chunk ∧
      chunk.val = bytes.val.take 32 := by
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
                                  cases xs with
                                  | nil => simp at bound
                                  | cons b16 xs =>
                                    cases xs with
                                    | nil => simp at bound
                                    | cons b17 xs =>
                                      cases xs with
                                      | nil => simp at bound
                                      | cons b18 xs =>
                                        cases xs with
                                        | nil => simp at bound
                                        | cons b19 xs =>
                                          cases xs with
                                          | nil => simp at bound
                                          | cons b20 xs =>
                                            cases xs with
                                            | nil => simp at bound
                                            | cons b21 xs =>
                                              cases xs with
                                              | nil => simp at bound
                                              | cons b22 xs =>
                                                cases xs with
                                                | nil => simp at bound
                                                | cons b23 xs =>
                                                  cases xs with
                                                  | nil => simp at bound
                                                  | cons b24 xs =>
                                                    cases xs with
                                                    | nil => simp at bound
                                                    | cons b25 xs =>
                                                      cases xs with
                                                      | nil => simp at bound
                                                      | cons b26 xs =>
                                                        cases xs with
                                                        | nil => simp at bound
                                                        | cons b27 xs =>
                                                          cases xs with
                                                          | nil => simp at bound
                                                          | cons b28 xs =>
                                                            cases xs with
                                                            | nil => simp at bound
                                                            | cons b29 xs =>
                                                              cases xs with
                                                              | nil => simp at bound
                                                              | cons b30 xs =>
                                                                cases xs with
                                                                | nil => simp at bound
                                                                | cons b31 xs =>
                                                                  simp only [MultiproofConeRef.reference.read32, Slice.index_usize,
                                                                    Slice.getElem?_Usize_eq, hxs]
                                                                  simp only [show (0#usize).val = 0 from rfl, show (1#usize).val = 1 from rfl, show (2#usize).val = 2 from rfl, show (3#usize).val = 3 from rfl, show (4#usize).val = 4 from rfl, show (5#usize).val = 5 from rfl, show (6#usize).val = 6 from rfl, show (7#usize).val = 7 from rfl, show (8#usize).val = 8 from rfl, show (9#usize).val = 9 from rfl, show (10#usize).val = 10 from rfl, show (11#usize).val = 11 from rfl, show (12#usize).val = 12 from rfl, show (13#usize).val = 13 from rfl, show (14#usize).val = 14 from rfl, show (15#usize).val = 15 from rfl, show (16#usize).val = 16 from rfl, show (17#usize).val = 17 from rfl, show (18#usize).val = 18 from rfl, show (19#usize).val = 19 from rfl, show (20#usize).val = 20 from rfl, show (21#usize).val = 21 from rfl, show (22#usize).val = 22 from rfl, show (23#usize).val = 23 from rfl, show (24#usize).val = 24 from rfl, show (25#usize).val = 25 from rfl, show (26#usize).val = 26 from rfl, show (27#usize).val = 27 from rfl, show (28#usize).val = 28 from rfl, show (29#usize).val = 29 from rfl, show (30#usize).val = 30 from rfl, show (31#usize).val = 31 from rfl,
                                                                    List.getElem?_cons_zero, List.getElem?_cons_succ, bind_tc_ok]
                                                                  exact ⟨_,rfl,rfl⟩

#print axioms read32_total
end AspisR1.MultiproofConeRead32
