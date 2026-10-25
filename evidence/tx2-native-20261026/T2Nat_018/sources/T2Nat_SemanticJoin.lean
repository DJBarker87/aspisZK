import T2Nat_ScalarJoin
import Port5Q2_ReaderSemantic
set_option autoImplicit false
noncomputable section
namespace AspisR1.T2Nat_SemanticJoin
open Aeneas Aeneas.Std Result AspisR1Stage2
open T2Nat_ResultEq

theorem congr (left right : CheckpointBytes4Sections.ReadK)
    (same : ∀ r, EqOk (left r) (right r)) (bytes : Slice U8) (at1 : Usize) :
    EqOk (Port5Q2_ReaderSemantic.semantic left bytes at1)
      (Port5Q2_ReaderSemantic.semantic right bytes at1) := by
  unfold Port5Q2_ReaderSemantic.semantic
  apply T2Nat_ResultEq.bind (same _)
  intro pair0
  rcases pair0 with ⟨value0,reader0⟩
  cases value0 with
  | Err e => exact T2Nat_ResultEq.refl _
  | Ok x0 =>
    simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok,Aeneas.Std.uncurry]
    apply T2Nat_ResultEq.bind (same _)
    intro pair1
    rcases pair1 with ⟨value1,reader1⟩
    cases value1 with
    | Err e => exact T2Nat_ResultEq.refl _
    | Ok x1 =>
      simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok,Aeneas.Std.uncurry]
      apply T2Nat_ResultEq.bind (same _)
      intro pair2
      rcases pair2 with ⟨value2,reader2⟩
      cases value2 with
      | Err e => exact T2Nat_ResultEq.refl _
      | Ok x2 =>
        simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok,Aeneas.Std.uncurry]
        apply T2Nat_ResultEq.bind (same _)
        intro pair3
        rcases pair3 with ⟨value3,reader3⟩
        cases value3 with
        | Err e => exact T2Nat_ResultEq.refl _
        | Ok x3 =>
          simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok,Aeneas.Std.uncurry]
          apply T2Nat_ResultEq.bind (same _)
          intro pair4
          rcases pair4 with ⟨value4,reader4⟩
          cases value4 with
          | Err e => exact T2Nat_ResultEq.refl _
          | Ok x4 =>
            simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok,Aeneas.Std.uncurry]
            apply T2Nat_ResultEq.bind (same _)
            intro pair5
            rcases pair5 with ⟨value5,reader5⟩
            cases value5 with
            | Err e => exact T2Nat_ResultEq.refl _
            | Ok x5 =>
              simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok,Aeneas.Std.uncurry]
              apply T2Nat_ResultEq.bind (same _)
              intro pair6
              rcases pair6 with ⟨value6,reader6⟩
              cases value6 with
              | Err e => exact T2Nat_ResultEq.refl _
              | Ok x6 =>
                simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok,Aeneas.Std.uncurry]
                apply T2Nat_ResultEq.bind (same _)
                intro pair7
                rcases pair7 with ⟨value7,reader7⟩
                cases value7 with
                | Err e => exact T2Nat_ResultEq.refl _
                | Ok x7 =>
                  simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok,Aeneas.Std.uncurry]
                  apply T2Nat_ResultEq.bind (same _)
                  intro pair8
                  rcases pair8 with ⟨value8,reader8⟩
                  cases value8 with
                  | Err e => exact T2Nat_ResultEq.refl _
                  | Ok x8 =>
                    simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok,Aeneas.Std.uncurry]
                    apply T2Nat_ResultEq.bind (same _)
                    intro pair9
                    rcases pair9 with ⟨value9,reader9⟩
                    cases value9 with
                    | Err e => exact T2Nat_ResultEq.refl _
                    | Ok x9 =>
                      simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok,Aeneas.Std.uncurry]
                      exact T2Nat_ResultEq.refl _


theorem reference (unwrap : T2Nat_RawJoin.Unwrap)
    (unwrap_ok : ∀ N b, unwrap N (.Ok b)=ok b) (bytes : Slice U8) (start : Usize) :
    EqOk (Port5Q2_ReaderSemantic.semantic (T2Nat_ScalarJoin.readK unwrap) bytes start)
      (CheckpointBytes4Ops.readSemanticAlpha bytes start) := by
  have relation := congr (T2Nat_ScalarJoin.readK unwrap) CheckpointBytes3Reader.readK
    (T2Nat_ScalarJoin.k_eq unwrap unwrap_ok) bytes start
  have eq := Port5Q2_ReaderSemantic.normalization CheckpointBytes3Reader.readK bytes start
  rw [eq] at relation
  exact relation

#print axioms congr
#print axioms reference
end AspisR1.T2Nat_SemanticJoin
end
