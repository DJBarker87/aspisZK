import R1Z.PV_CB_ProducerLocalLimb
import R1Z.PV_CB_ProducerRead
import R1Z.PV_CB_ProducerTry
import R1Z.PV_CB_ProducerMake16
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_CB_ProducerLocalTuple
open Aeneas Aeneas.Std Result ProverRwFull PV_CB_ProducerLimb
variable [ExternalTypes]
attribute [local irreducible] PV_CB_ProducerPost.Good
abbrev Tuple := aspis_statement.pool_v1.pair_trace.PoolV1PairCopyTupleV1

theorem tuple (ops : ExternalFuns) (trace : Trace) (input : Tuple)
    (vt : PV_CB_CanonicalArrays.Valid (PV_CB_ProducerLocalLimb.Reads trace) input.limbs)
    (vo : PV_CB_CanonicalArrays.Valid OffsetValid input.limbs) :
    PV_CB_ProducerPost.Good (PV_CB_CanonicalArrays.Valid PV_CB_CanonicalM31.Valid)
      (@host_semantic.copy_tuple_values _ (ProverRwDictionaryScalar.selected ops) trace input) := by
  unfold host_semantic.copy_tuple_values
  apply PV_CB_ProducerBind.bind
  intro limb0 read0
  apply PV_CB_ProducerBind.bind
  intro result0 resultRead0
  cases result0 with
  | Err err => exact PV_CB_ProducerPost.error _ _
  | Ok value0 =>
    have post0 := PV_CB_ProducerLocalLimb.limb ops trace limb0
      (vt limb0 (PV_CB_ProducerRead.array_mem input.limbs 0#usize limb0 read0))
      (vo limb0 (PV_CB_ProducerRead.array_mem input.limbs 0#usize limb0 read0))
    unfold PV_CB_ProducerPost.Good at post0
    have valid0 := post0 value0 resultRead0
    simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok]
    apply PV_CB_ProducerBind.bind
    intro limb1 read1
    apply PV_CB_ProducerBind.bind
    intro result1 resultRead1
    cases result1 with
    | Err err => exact PV_CB_ProducerPost.error _ _
    | Ok value1 =>
      have post1 := PV_CB_ProducerLocalLimb.limb ops trace limb1
        (vt limb1 (PV_CB_ProducerRead.array_mem input.limbs 1#usize limb1 read1))
        (vo limb1 (PV_CB_ProducerRead.array_mem input.limbs 1#usize limb1 read1))
      unfold PV_CB_ProducerPost.Good at post1
      have valid1 := post1 value1 resultRead1
      simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok]
      apply PV_CB_ProducerBind.bind
      intro limb2 read2
      apply PV_CB_ProducerBind.bind
      intro result2 resultRead2
      cases result2 with
      | Err err => exact PV_CB_ProducerPost.error _ _
      | Ok value2 =>
        have post2 := PV_CB_ProducerLocalLimb.limb ops trace limb2
          (vt limb2 (PV_CB_ProducerRead.array_mem input.limbs 2#usize limb2 read2))
          (vo limb2 (PV_CB_ProducerRead.array_mem input.limbs 2#usize limb2 read2))
        unfold PV_CB_ProducerPost.Good at post2
        have valid2 := post2 value2 resultRead2
        simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok]
        apply PV_CB_ProducerBind.bind
        intro limb3 read3
        apply PV_CB_ProducerBind.bind
        intro result3 resultRead3
        cases result3 with
        | Err err => exact PV_CB_ProducerPost.error _ _
        | Ok value3 =>
          have post3 := PV_CB_ProducerLocalLimb.limb ops trace limb3
            (vt limb3 (PV_CB_ProducerRead.array_mem input.limbs 3#usize limb3 read3))
            (vo limb3 (PV_CB_ProducerRead.array_mem input.limbs 3#usize limb3 read3))
          unfold PV_CB_ProducerPost.Good at post3
          have valid3 := post3 value3 resultRead3
          simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok]
          apply PV_CB_ProducerBind.bind
          intro limb4 read4
          apply PV_CB_ProducerBind.bind
          intro result4 resultRead4
          cases result4 with
          | Err err => exact PV_CB_ProducerPost.error _ _
          | Ok value4 =>
            have post4 := PV_CB_ProducerLocalLimb.limb ops trace limb4
              (vt limb4 (PV_CB_ProducerRead.array_mem input.limbs 4#usize limb4 read4))
              (vo limb4 (PV_CB_ProducerRead.array_mem input.limbs 4#usize limb4 read4))
            unfold PV_CB_ProducerPost.Good at post4
            have valid4 := post4 value4 resultRead4
            simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok]
            apply PV_CB_ProducerBind.bind
            intro limb5 read5
            apply PV_CB_ProducerBind.bind
            intro result5 resultRead5
            cases result5 with
            | Err err => exact PV_CB_ProducerPost.error _ _
            | Ok value5 =>
              have post5 := PV_CB_ProducerLocalLimb.limb ops trace limb5
                (vt limb5 (PV_CB_ProducerRead.array_mem input.limbs 5#usize limb5 read5))
                (vo limb5 (PV_CB_ProducerRead.array_mem input.limbs 5#usize limb5 read5))
              unfold PV_CB_ProducerPost.Good at post5
              have valid5 := post5 value5 resultRead5
              simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok]
              apply PV_CB_ProducerBind.bind
              intro limb6 read6
              apply PV_CB_ProducerBind.bind
              intro result6 resultRead6
              cases result6 with
              | Err err => exact PV_CB_ProducerPost.error _ _
              | Ok value6 =>
                have post6 := PV_CB_ProducerLocalLimb.limb ops trace limb6
                  (vt limb6 (PV_CB_ProducerRead.array_mem input.limbs 6#usize limb6 read6))
                  (vo limb6 (PV_CB_ProducerRead.array_mem input.limbs 6#usize limb6 read6))
                unfold PV_CB_ProducerPost.Good at post6
                have valid6 := post6 value6 resultRead6
                simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok]
                apply PV_CB_ProducerBind.bind
                intro limb7 read7
                apply PV_CB_ProducerBind.bind
                intro result7 resultRead7
                cases result7 with
                | Err err => exact PV_CB_ProducerPost.error _ _
                | Ok value7 =>
                  have post7 := PV_CB_ProducerLocalLimb.limb ops trace limb7
                    (vt limb7 (PV_CB_ProducerRead.array_mem input.limbs 7#usize limb7 read7))
                    (vo limb7 (PV_CB_ProducerRead.array_mem input.limbs 7#usize limb7 read7))
                  unfold PV_CB_ProducerPost.Good at post7
                  have valid7 := post7 value7 resultRead7
                  simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok]
                  apply PV_CB_ProducerBind.bind
                  intro limb8 read8
                  apply PV_CB_ProducerBind.bind
                  intro result8 resultRead8
                  cases result8 with
                  | Err err => exact PV_CB_ProducerPost.error _ _
                  | Ok value8 =>
                    have post8 := PV_CB_ProducerLocalLimb.limb ops trace limb8
                      (vt limb8 (PV_CB_ProducerRead.array_mem input.limbs 8#usize limb8 read8))
                      (vo limb8 (PV_CB_ProducerRead.array_mem input.limbs 8#usize limb8 read8))
                    unfold PV_CB_ProducerPost.Good at post8
                    have valid8 := post8 value8 resultRead8
                    simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok]
                    apply PV_CB_ProducerBind.bind
                    intro limb9 read9
                    apply PV_CB_ProducerBind.bind
                    intro result9 resultRead9
                    cases result9 with
                    | Err err => exact PV_CB_ProducerPost.error _ _
                    | Ok value9 =>
                      have post9 := PV_CB_ProducerLocalLimb.limb ops trace limb9
                        (vt limb9 (PV_CB_ProducerRead.array_mem input.limbs 9#usize limb9 read9))
                        (vo limb9 (PV_CB_ProducerRead.array_mem input.limbs 9#usize limb9 read9))
                      unfold PV_CB_ProducerPost.Good at post9
                      have valid9 := post9 value9 resultRead9
                      simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok]
                      apply PV_CB_ProducerBind.bind
                      intro limb10 read10
                      apply PV_CB_ProducerBind.bind
                      intro result10 resultRead10
                      cases result10 with
                      | Err err => exact PV_CB_ProducerPost.error _ _
                      | Ok value10 =>
                        have post10 := PV_CB_ProducerLocalLimb.limb ops trace limb10
                          (vt limb10 (PV_CB_ProducerRead.array_mem input.limbs 10#usize limb10 read10))
                          (vo limb10 (PV_CB_ProducerRead.array_mem input.limbs 10#usize limb10 read10))
                        unfold PV_CB_ProducerPost.Good at post10
                        have valid10 := post10 value10 resultRead10
                        simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok]
                        apply PV_CB_ProducerBind.bind
                        intro limb11 read11
                        apply PV_CB_ProducerBind.bind
                        intro result11 resultRead11
                        cases result11 with
                        | Err err => exact PV_CB_ProducerPost.error _ _
                        | Ok value11 =>
                          have post11 := PV_CB_ProducerLocalLimb.limb ops trace limb11
                            (vt limb11 (PV_CB_ProducerRead.array_mem input.limbs 11#usize limb11 read11))
                            (vo limb11 (PV_CB_ProducerRead.array_mem input.limbs 11#usize limb11 read11))
                          unfold PV_CB_ProducerPost.Good at post11
                          have valid11 := post11 value11 resultRead11
                          simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok]
                          apply PV_CB_ProducerBind.bind
                          intro limb12 read12
                          apply PV_CB_ProducerBind.bind
                          intro result12 resultRead12
                          cases result12 with
                          | Err err => exact PV_CB_ProducerPost.error _ _
                          | Ok value12 =>
                            have post12 := PV_CB_ProducerLocalLimb.limb ops trace limb12
                              (vt limb12 (PV_CB_ProducerRead.array_mem input.limbs 12#usize limb12 read12))
                              (vo limb12 (PV_CB_ProducerRead.array_mem input.limbs 12#usize limb12 read12))
                            unfold PV_CB_ProducerPost.Good at post12
                            have valid12 := post12 value12 resultRead12
                            simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok]
                            apply PV_CB_ProducerBind.bind
                            intro limb13 read13
                            apply PV_CB_ProducerBind.bind
                            intro result13 resultRead13
                            cases result13 with
                            | Err err => exact PV_CB_ProducerPost.error _ _
                            | Ok value13 =>
                              have post13 := PV_CB_ProducerLocalLimb.limb ops trace limb13
                                (vt limb13 (PV_CB_ProducerRead.array_mem input.limbs 13#usize limb13 read13))
                                (vo limb13 (PV_CB_ProducerRead.array_mem input.limbs 13#usize limb13 read13))
                              unfold PV_CB_ProducerPost.Good at post13
                              have valid13 := post13 value13 resultRead13
                              simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok]
                              apply PV_CB_ProducerBind.bind
                              intro limb14 read14
                              apply PV_CB_ProducerBind.bind
                              intro result14 resultRead14
                              cases result14 with
                              | Err err => exact PV_CB_ProducerPost.error _ _
                              | Ok value14 =>
                                have post14 := PV_CB_ProducerLocalLimb.limb ops trace limb14
                                  (vt limb14 (PV_CB_ProducerRead.array_mem input.limbs 14#usize limb14 read14))
                                  (vo limb14 (PV_CB_ProducerRead.array_mem input.limbs 14#usize limb14 read14))
                                unfold PV_CB_ProducerPost.Good at post14
                                have valid14 := post14 value14 resultRead14
                                simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok]
                                apply PV_CB_ProducerBind.bind
                                intro limb15 read15
                                apply PV_CB_ProducerBind.bind
                                intro result15 resultRead15
                                cases result15 with
                                | Err err => exact PV_CB_ProducerPost.error _ _
                                | Ok value15 =>
                                  have post15 := PV_CB_ProducerLocalLimb.limb ops trace limb15
                                    (vt limb15 (PV_CB_ProducerRead.array_mem input.limbs 15#usize limb15 read15))
                                    (vo limb15 (PV_CB_ProducerRead.array_mem input.limbs 15#usize limb15 read15))
                                  unfold PV_CB_ProducerPost.Good at post15
                                  have valid15 := post15 value15 resultRead15
                                  simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok]
                                  apply PV_CB_ProducerPost.pure
                                  exact PV_CB_ProducerMake16.valid value0 value1 value2 value3 value4 value5 value6 value7 value8 value9 value10 value11 value12 value13 value14 value15
                                    valid0 valid1 valid2 valid3 valid4 valid5 valid6 valid7 valid8 valid9 valid10 valid11 valid12 valid13 valid14 valid15
#print axioms tuple
end R1Z.PV_CB_ProducerLocalTuple
