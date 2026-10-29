import R1Z.PV_RunJoin_CircleProduced51
import R1Z.PV_RunJoin_PostEquation60
import R1Z.PV_RunJoin_RoundCanonicalComplete51
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_BackendBuildTrace60
open Aeneas Aeneas.Std Result ProverRwFull
open PV_RunJoin_WeightInstalled46 PV_RunJoin_ResultPost41
open PV_RunJoin_PointPrefix51 (Prefix)
abbrev Q := ProverRwFull.aspis_core.field.QM31

def Trace [ExternalTypes] [ExternalFuns] {H T : Type} (commitInst : host_semantic.Commitments T)
    (c1 : Array (alloc.vec.Vec aspis_core.field.M31) 26#usize)
    (d g : Array Q 1024#usize) (initial next : T) (built : host_semantic.BuiltSemantics H) : Prop :=
  ∃ (first : T) (root1 root2 : Array U8 32#usize) (h : alloc.vec.Vec Q),
    commitInst.c1 initial c1 d=ok (.Ok root1,first) ∧
    commitInst.c2 first (alloc.vec.Vec.deref h) g=ok (.Ok root2,next) ∧
    host_semantic.lift_columns c1 h g d=ok built.columns

theorem complete (base : ExternalTypes) (heap : Heap) (box : Box) (ops : @ExternalFuns (types base))
    {H T1 T2 : Type} (D : aspis_core.digest.Digest32 H)
    (helperInst : core.ops.function.FnOnce T1 (Q × Q) (core.result.Result (alloc.vec.Vec Q) r1_wire.Error))
    (commitInst : host_semantic.Commitments T2)
    (public1 : @aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public (types base))
    (c1 : Array (alloc.vec.Vec aspis_core.field.M31) 26#usize)
    (d g padding : Array Q 1024#usize) (helper : T1) (commitments : T2) (hash : H) (variant : transport.Variant) :
    Post (fun pair => match pair.1 with | .Err _ => True | .Ok built => @Trace (types base) (selected base heap box ops) H T2 commitInst c1 d g commitments pair.2 built)
      (@host_semantic.build_with_helper_mode (types base) (selected base heap box ops)
        H T1 T2 D helperInst commitInst public1 c1 d g padding helper commitments hash variant) := by
  letI : ExternalTypes := types base
  letI : ExternalFuns := selected base heap box ops
  unfold host_semantic.build_with_helper_mode
  apply PV_RunJoin_ResultPost41.bind
  intro checked
  cases checked with
  | Err e => trivial
  | Ok checkedUnit =>
    try simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok,lift,Aeneas.Std.uncurry,bind_assoc_eq]
    apply PV_RunJoin_PostEquation60.bind
    intro committed hcommitted
    rcases committed with ⟨rootStatus,commit1⟩
    cases rootStatus with
    | Err e => trivial
    | Ok root1 =>
      try simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok,lift,Aeneas.Std.uncurry,bind_assoc_eq]
      apply PV_RunJoin_ResultPost41.bind
      intro publicBytes
      apply PV_RunJoin_ResultPost41.bind
      intro mappedPublic
      cases mappedPublic with
      | Err e => trivial
      | Ok pubBytes =>
        try simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok,lift,Aeneas.Std.uncurry,bind_assoc_eq]
        apply PV_RunJoin_ResultPost41.bind
        intro newTranscript
        cases newTranscript with
        | Err e => trivial
        | Ok t0 =>
          try simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok,lift,Aeneas.Std.uncurry,bind_assoc_eq]
          apply PV_RunJoin_ResultPost41.bind
          intro b0
          try simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok,lift,Aeneas.Std.uncurry,bind_assoc_eq]
          apply PV_RunJoin_ResultPost41.bind
          intro triple0
          rcases triple0 with ⟨status0,t1,b1⟩
          cases status0 with
          | Err e => trivial
          | Ok lambda =>
            try simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok,lift,Aeneas.Std.uncurry,bind_assoc_eq]
            apply PV_RunJoin_ResultPost41.bind
            intro triple1
            rcases triple1 with ⟨status1,t2,b2⟩
            cases status1 with
            | Err e => trivial
            | Ok chi =>
              try simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok,lift,Aeneas.Std.uncurry,bind_assoc_eq]
              apply PV_RunJoin_ResultPost41.bind
              intro helperResult
              cases helperResult with
              | Err e => trivial
              | Ok helperValues =>
                try simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok,lift,Aeneas.Std.uncurry,bind_assoc_eq]
                apply PV_RunJoin_ResultPost41.bind
                intro padded
                rcases padded with ⟨paddingResult,paddedSlice⟩
                apply PV_RunJoin_ResultPost41.bind
                intro mappedPadding
                cases mappedPadding with
                | Err e => trivial
                | Ok paddingUnit =>
                  try simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok,lift,Aeneas.Std.uncurry,bind_assoc_eq]
                  split
                  · trivial
                  ·
                    apply PV_RunJoin_ResultPost41.bind
                    intro helperSum
                    apply PV_RunJoin_ResultPost41.bind
                    intro zero
                    apply PV_RunJoin_ResultPost41.bind
                    intro sumDifferent
                    cases sumDifferent with
                    | true => trivial
                    | false =>
                      try simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok,lift,Aeneas.Std.uncurry,bind_assoc_eq]
                      apply PV_RunJoin_PostEquation60.bind
                      intro committed2 hcommitted2
                      rcases committed2 with ⟨rootStatus2,commit2⟩
                      cases rootStatus2 with
                      | Err e => trivial
                      | Ok root2 =>
                        try simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok,lift,Aeneas.Std.uncurry,bind_assoc_eq]
                        apply PV_RunJoin_ResultPost41.bind
                        intro triple2
                        rcases triple2 with ⟨status2,t3,b3⟩
                        cases status2 with
                        | Err e => trivial
                        | Ok theta =>
                          try simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok,lift,Aeneas.Std.uncurry,bind_assoc_eq]
                          apply PV_RunJoin_ResultPost41.bind
                          intro zeroRows
                          rcases zeroRows with ⟨zeroStatus,t4,b4⟩
                          cases zeroStatus with
                          | Err e => trivial
                          | Ok zc =>
                            try simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok,lift,Aeneas.Std.uncurry,bind_assoc_eq]
                            apply PV_RunJoin_ResultPost41.bind
                            intro triple13
                            rcases triple13 with ⟨status13,t5,b5⟩
                            cases status13 with
                            | Err e => trivial
                            | Ok mu =>
                              try simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok,lift,Aeneas.Std.uncurry,bind_assoc_eq]
                              apply PV_RunJoin_PostEquation60.bind
                              intro columns hcolumns
                              apply PV_RunJoin_ResultPost41.bind
                              intro dc
                              apply PV_RunJoin_ResultPost41.bind
                              intro maskSum
                              apply PV_RunJoin_ResultPost41.bind
                              intro maskSum1
                              apply PV_RunJoin_ResultPost41.bind
                              intro wide
                              apply PV_RunJoin_ResultPost41.bind
                              intro encoded
                              try simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok,lift,Aeneas.Std.uncurry,bind_assoc_eq]
                              apply PV_RunJoin_ResultPost41.bind
                              intro triple14
                              rcases triple14 with ⟨status14,t6,b6⟩
                              cases status14 with
                              | Err e => trivial
                              | Ok eta =>
                                try simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok,lift,Aeneas.Std.uncurry,bind_assoc_eq]
                                apply PV_RunJoin_ResultPost41.bind
                                intro sumcheck
                                rcases sumcheck with ⟨sumcheckStatus,t7,b7⟩
                                cases sumcheckStatus with
                                | Err e => trivial
                                | Ok pointRunning =>
                                  try simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok,lift,Aeneas.Std.uncurry,bind_assoc_eq]
                                  rcases pointRunning with ⟨alpha,running⟩
                                  apply PV_RunJoin_ResultPost41.bind
                                  intro claimsStatus
                                  cases claimsStatus with
                                  | Err e => trivial
                                  | Ok claims =>
                                    try simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok,lift,Aeneas.Std.uncurry,bind_assoc_eq]
                                    apply PV_RunJoin_ResultPost41.bind
                                    intro stateBefore
                                    apply PV_RunJoin_ResultPost41.bind
                                    intro alpha8
                                    apply PV_RunJoin_ResultPost41.bind
                                    intro alpha9
                                    apply PV_RunJoin_ResultPost41.bind
                                    intro extras
                                    apply PV_RunJoin_ResultPost41.bind
                                    intro claimBytes
                                    apply PV_RunJoin_ResultPost41.bind
                                    intro record25
                                    cases record25 with
                                    | Err e => trivial
                                    | Ok framed25 =>
                                      try simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok,lift,Aeneas.Std.uncurry,bind_assoc_eq]
                                      apply PV_RunJoin_RecordAppend41.bind_post (PV_RunJoin_ResultWitness51.complete _)
                                      intro circle25 h25
                                      rcases circle25 with ⟨circleStatus25,t8⟩
                                      cases circleStatus25 with
                                      | Err e => trivial
                                      | Ok z0 =>
                                        try simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok,lift,Aeneas.Std.uncurry,bind_assoc_eq]
                                        apply PV_RunJoin_ResultPost41.bind
                                        intro b8
                                        apply PV_RunJoin_ResultPost41.bind
                                        intro endpoint
                                        apply PV_RunJoin_ResultPost41.bind
                                        intro record26
                                        cases record26 with
                                        | Err e => trivial
                                        | Ok framed26 =>
                                          try simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok,lift,Aeneas.Std.uncurry,bind_assoc_eq]
                                          apply PV_RunJoin_RecordAppend41.bind_post (PV_RunJoin_ResultWitness51.complete _)
                                          intro circle26 h26
                                          rcases circle26 with ⟨circleStatus26,t9⟩
                                          cases circleStatus26 with
                                          | Err e => trivial
                                          | Ok z1 =>
                                            try simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok,lift,Aeneas.Std.uncurry,bind_assoc_eq]
                                            apply PV_RunJoin_ResultPost41.bind
                                            intro b9
                                            apply PV_RunJoin_ResultPost41.bind
                                            intro equalPoints
                                            cases equalPoints with
                                            | true => trivial
                                            | false =>
                                              try simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok,lift,Aeneas.Std.uncurry,bind_assoc_eq]
                                              exact ⟨commit1,root1,root2,_,hcommitted,hcommitted2,hcolumns⟩
#print axioms complete
end R1Z.PV_RunJoin_BackendBuildTrace60
