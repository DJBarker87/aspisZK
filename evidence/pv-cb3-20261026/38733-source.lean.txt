import R1Z.PV_CB3_StagedTotal
set_option autoImplicit false
namespace R1Z.PV_CB3_Array32
open Aeneas Aeneas.Std
/-- Fixed byte-carrier shape; this never evaluates a sampler recurrence. -/
theorem view (block : Array U8 32#usize) :
    ∃ a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24 a25 a26 a27 a28 a29 a30 a31 : U8,
      block = Array.make 32#usize [a0,a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14,a15,a16,a17,a18,a19,a20,a21,a22,a23,a24,a25,a26,a27,a28,a29,a30,a31] := by
  rcases block with ⟨xs,hlen⟩
  cases xs with
  | nil => simp at hlen
  | cons a0 xs =>
    cases xs with
    | nil => simp at hlen
    | cons a1 xs =>
      cases xs with
      | nil => simp at hlen
      | cons a2 xs =>
        cases xs with
        | nil => simp at hlen
        | cons a3 xs =>
          cases xs with
          | nil => simp at hlen
          | cons a4 xs =>
            cases xs with
            | nil => simp at hlen
            | cons a5 xs =>
              cases xs with
              | nil => simp at hlen
              | cons a6 xs =>
                cases xs with
                | nil => simp at hlen
                | cons a7 xs =>
                  cases xs with
                  | nil => simp at hlen
                  | cons a8 xs =>
                    cases xs with
                    | nil => simp at hlen
                    | cons a9 xs =>
                      cases xs with
                      | nil => simp at hlen
                      | cons a10 xs =>
                        cases xs with
                        | nil => simp at hlen
                        | cons a11 xs =>
                          cases xs with
                          | nil => simp at hlen
                          | cons a12 xs =>
                            cases xs with
                            | nil => simp at hlen
                            | cons a13 xs =>
                              cases xs with
                              | nil => simp at hlen
                              | cons a14 xs =>
                                cases xs with
                                | nil => simp at hlen
                                | cons a15 xs =>
                                  cases xs with
                                  | nil => simp at hlen
                                  | cons a16 xs =>
                                    cases xs with
                                    | nil => simp at hlen
                                    | cons a17 xs =>
                                      cases xs with
                                      | nil => simp at hlen
                                      | cons a18 xs =>
                                        cases xs with
                                        | nil => simp at hlen
                                        | cons a19 xs =>
                                          cases xs with
                                          | nil => simp at hlen
                                          | cons a20 xs =>
                                            cases xs with
                                            | nil => simp at hlen
                                            | cons a21 xs =>
                                              cases xs with
                                              | nil => simp at hlen
                                              | cons a22 xs =>
                                                cases xs with
                                                | nil => simp at hlen
                                                | cons a23 xs =>
                                                  cases xs with
                                                  | nil => simp at hlen
                                                  | cons a24 xs =>
                                                    cases xs with
                                                    | nil => simp at hlen
                                                    | cons a25 xs =>
                                                      cases xs with
                                                      | nil => simp at hlen
                                                      | cons a26 xs =>
                                                        cases xs with
                                                        | nil => simp at hlen
                                                        | cons a27 xs =>
                                                          cases xs with
                                                          | nil => simp at hlen
                                                          | cons a28 xs =>
                                                            cases xs with
                                                            | nil => simp at hlen
                                                            | cons a29 xs =>
                                                              cases xs with
                                                              | nil => simp at hlen
                                                              | cons a30 xs =>
                                                                cases xs with
                                                                | nil => simp at hlen
                                                                | cons a31 xs =>
                                                                  have hz : xs.length = 0 := by
                                                                    simp only [List.length_cons] at hlen
                                                                    change xs.length + 32 = 32 at hlen
                                                                    omega
                                                                  have he : xs = [] := List.length_eq_zero_iff.mp hz
                                                                  subst xs
                                                                  exact ⟨a0,a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14,a15,a16,a17,a18,a19,a20,a21,a22,a23,a24,a25,a26,a27,a28,a29,a30,a31,rfl⟩
#print axioms view
end R1Z.PV_CB3_Array32
