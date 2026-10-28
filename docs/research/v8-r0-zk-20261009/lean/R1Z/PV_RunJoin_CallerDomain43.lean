import R1Z.PV_RunJoin_LayoutPieces43
import R1Z.PV_RunJoin_CanonicalAppend43
import R1Z.PV_RunJoin_ZeroComplete43
import R1Z.PV_RunJoin_RoundComplete43
import R1Z.PV_RunJoin_CloneBytes43
import R1Z.PV_RunJoin_ClaimCanonical41
import R1Z.PV_RunJoin_EndpointCanonical41
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_CallerDomain43
open Aeneas Aeneas.Std Result ProverRwFull PV_RunJoin_ResultPost41
variable [ExternalTypes]
abbrev Q := aspis_core.field.QM31

theorem post (ops : ExternalFuns) {H T1 T2 : Type}
    (hash : aspis_core.digest.Digest32 H)
    (helperInst : core.ops.function.FnOnce T1 (Q × Q)
      (core.result.Result (alloc.vec.Vec Q) r1_wire.Error))
    (commitInst : host_semantic.Commitments T2)
    (public1 : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (c1 : Array (alloc.vec.Vec aspis_core.field.M31) 26#usize)
    (d g padding : Array Q 1024#usize) (helper : T1) (commitments : T2)
    (initialHash : H) (variant : transport.Variant) :
    Post (fun next : (core.result.Result (host_semantic.BuiltSemantics H) r1_wire.Error) × T2 =>
      match next.1 with
      | .Err _ => True
      | .Ok built => built.bytes.length=13831 ∧ ∃ records, PV_RunJoin_SemanticDomain40.Domain ops
          (alloc.vec.Vec.deref built.bytes) 27#u8 32#usize 0#u8 records)
      (@host_semantic.build_with_helper_mode _ (ProverRwP6BodyCandidate.selected ops)
        H T1 T2 hash helperInst commitInst public1 c1 d g padding helper commitments initialHash variant) := by
  letI : ExternalFuns := ProverRwP6BodyCandidate.selected ops
  unfold host_semantic.build_with_helper_mode
  apply PV_RunJoin_ResultPost41.bind
  intro checked
  cases checked with
  | Err error => trivial
  | Ok checkedValue =>
    try simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok,lift,Aeneas.Std.uncurry,bind_assoc_eq]
    apply PV_RunJoin_ResultPost41.bind
    intro committed
    rcases committed with ⟨rootResult,commit1⟩
    cases rootResult with
    | Err error => trivial
    | Ok root1 =>
      try simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok,lift,Aeneas.Std.uncurry,bind_assoc_eq]
      apply PV_RunJoin_ResultPost41.bind
      intro publicBytes
      apply PV_RunJoin_ResultPost41.bind
      intro mappedPublic
      cases mappedPublic with
      | Err error => trivial
      | Ok pubBytes =>
        try simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok,lift,Aeneas.Std.uncurry,bind_assoc_eq]
        apply PV_RunJoin_ResultPost41.bind
        intro newTranscript
        cases newTranscript with
        | Err error => trivial
        | Ok t0 =>
          try simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok,lift,Aeneas.Std.uncurry,bind_assoc_eq]
          try simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok,lift,Aeneas.Std.uncurry,bind_assoc_eq]
          obtain ⟨b0,hb0,vb0⟩ := PV_RunJoin_CloneBytes43.complete (Array.to_slice root1)
          rw [hb0]
          try simp only [bind_tc_ok,lift]
          have lb0 : b0.length=32 := by
            change b0.val.length=32
            rw [vb0]
            exact root1.property
          have rp := PV_RunJoin_RecordPost43.append ops hash 0#u8 0#u8 0#usize
            (Array.to_slice (Std.Array.empty U8)) t0 b0 (PV_RunJoin_RowShapes41.row0 ops) (rfl)
            (by change b0.length+5+0≤Usize.max;rw [lb0];scalar_tac)
          apply PV_RunJoin_RecordAppend41.bind_post rp
          intro triple0 hp0
          rcases triple0 with ⟨status0,t1,b1⟩
          cases status0 with
          | Err error => trivial
          | Ok challenge0 =>
            try simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok,lift,Aeneas.Std.uncurry,bind_assoc_eq]
            obtain ⟨head0,headlen0,hbytes0,lb1⟩ := hp0
            have lb1 : b1.length=37 := by
              rw [lb0] at lb1
              exact lb1
            have rp := PV_RunJoin_RecordPost43.append ops hash 1#u8 0#u8 0#usize
              (Array.to_slice (Std.Array.empty U8)) t1 b1 (PV_RunJoin_RowShapes41.row1 ops) (rfl)
              (by change b1.length+5+0≤Usize.max;rw [lb1];scalar_tac)
            apply PV_RunJoin_RecordAppend41.bind_post rp
            intro triple1 hp1
            rcases triple1 with ⟨status1,t2,b2⟩
            cases status1 with
            | Err error => trivial
            | Ok challenge1 =>
              try simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok,lift,Aeneas.Std.uncurry,bind_assoc_eq]
              obtain ⟨head1,headlen1,hbytes1,lb2⟩ := hp1
              have lb2 : b2.length=42 := by
                rw [lb1] at lb2
                exact lb2
              apply PV_RunJoin_ResultPost41.bind
              intro helperResult
              cases helperResult with
              | Err error => trivial
              | Ok helperValues =>
                try simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok,lift,Aeneas.Std.uncurry,bind_assoc_eq]
                try simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok,lift,Aeneas.Std.uncurry,bind_assoc_eq]
                apply PV_RunJoin_ResultPost41.bind
                intro padded
                rcases padded with ⟨paddingResult,paddedSlice⟩
                apply PV_RunJoin_ResultPost41.bind
                intro mappedPadding
                cases mappedPadding with
                | Err error => trivial
                | Ok paddingValue =>
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
                      apply PV_RunJoin_ResultPost41.bind
                      intro committed2
                      rcases committed2 with ⟨root2Result,commit2⟩
                      cases root2Result with
                      | Err error => trivial
                      | Ok root2 =>
                        try simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok,lift,Aeneas.Std.uncurry,bind_assoc_eq]
                        have rp := PV_RunJoin_RecordPost43.append ops hash 2#u8 1#u8 32#usize
                          (Array.to_slice root2) t2 b2 (PV_RunJoin_RowShapes41.row2 ops) (by rw [Array.length_to_slice];rfl)
                          (by change b2.length+5+32≤Usize.max;rw [lb2];scalar_tac)
                        apply PV_RunJoin_RecordAppend41.bind_post rp
                        intro triple2 hp2
                        rcases triple2 with ⟨status2,t3,b3⟩
                        cases status2 with
                        | Err error => trivial
                        | Ok challenge2 =>
                          try simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok,lift,Aeneas.Std.uncurry,bind_assoc_eq]
                          obtain ⟨head2,headlen2,hbytes2,lb3⟩ := hp2
                          have lb3 : b3.length=79 := by
                            rw [lb2] at lb3
                            exact lb3
                          have zp := PV_RunJoin_ZeroComplete43.post ops hash t3 b3
                            (by rw [lb3];scalar_tac)
                          apply PV_RunJoin_RecordAppend41.bind_post zp
                          intro zeroRows hz
                          rcases zeroRows with ⟨zeroResult,t4,b4⟩
                          cases zeroResult with
                          | Err error => trivial
                          | Ok zc =>
                            try simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok,lift,Aeneas.Std.uncurry,bind_assoc_eq]
                            have lb4 : b4.length=129 := by
                              have h := PV_RunJoin_ByteExtension43.length hz
                              change b4.val.length=129
                              rw [show b3.val.length=79 from lb3] at h
                              exact h
                            have rp := PV_RunJoin_RecordPost43.append ops hash 13#u8 0#u8 0#usize
                              (Array.to_slice (Std.Array.empty U8)) t4 b4 (PV_RunJoin_RowShapes41.row13 ops) (rfl)
                              (by change b4.length+5+0≤Usize.max;rw [lb4];scalar_tac)
                            apply PV_RunJoin_RecordAppend41.bind_post rp
                            intro triple13 hp13
                            rcases triple13 with ⟨status13,t5,b5⟩
                            cases status13 with
                            | Err error => trivial
                            | Ok challenge13 =>
                              try simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok,lift,Aeneas.Std.uncurry,bind_assoc_eq]
                              obtain ⟨head13,headlen13,hbytes13,lb5⟩ := hp13
                              have lb5 : b5.length=134 := by
                                rw [lb4] at lb5
                                exact lb5
                              apply PV_RunJoin_ResultPost41.bind
                              intro columns
                              apply PV_RunJoin_ResultPost41.bind
                              intro dc
                              apply PV_RunJoin_ResultPost41.bind
                              intro maskSum
                              apply PV_RunJoin_ResultPost41.bind
                              intro maskSum1
                              rw [PV_RunJoin_PolyCell38.embed ops maskSum1]
                              try simp only [bind_tc_ok]
                              rw [PV_RunJoin_FlatBytes35.installed ops (PV_RunJoin_PolyCell38.wide maskSum1)]
                              try simp only [bind_tc_ok,lift]
                              have mp := PV_RunJoin_CanonicalAppend43.post ops hash 14#u8 3#u8 32#usize
                                (Array.to_slice (PV_RunJoin_FlatBytes35.wire (PV_RunJoin_PolyCell38.wide maskSum1))) t5 b5
                                (PV_RunJoin_RowShapes41.row14 ops) rfl (by rw [lb5];scalar_tac)
                                (PV_RunJoin_HighCell41.high maskSum1)
                              apply PV_RunJoin_RecordAppend41.bind_post mp
                              intro maskRecord hm
                              rcases maskRecord with ⟨maskResult,t6,b6⟩
                              cases maskResult with
                              | Err error => trivial
                              | Ok eta =>
                                try simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok,lift,Aeneas.Std.uncurry,bind_assoc_eq]
                                have lb6 : b6.length=171 := by
                                  have h := PV_RunJoin_CanonicalRecord43.length hm
                                  change b6.val.length=171
                                  rw [show b5.val.length=134 from lb5] at h
                                  exact h
                                apply PV_RunJoin_RecordAppend41.bind_post
                                  (PV_RunJoin_RoundComplete43.post ops hash _ _ t6 b6 maskSum1 (by rw [lb6];scalar_tac))
                                intro sumcheck hs
                                rcases sumcheck with ⟨sumcheckResult,t7,b7⟩
                                cases sumcheckResult with
                                | Err error => trivial
                                | Ok pointRunning =>
                                  try simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok,lift,Aeneas.Std.uncurry,bind_assoc_eq]
                                  rcases pointRunning with ⟨alpha,running⟩
                                  change PV_RunJoin_RoundStream43.Stream b6.val 10 b7.val at hs
                                  have lb7 : b7.length=9181 := by
                                    have h := PV_RunJoin_RoundStream43.length hs
                                    change b7.val.length=9181
                                    rw [show b6.val.length=171 from lb6] at h
                                    exact h
                                  apply PV_RunJoin_ResultPost41.bind
                                  intro claimsResult
                                  cases claimsResult with
                                  | Err error => trivial
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
                                    obtain ⟨claimBytes,hclaim,claimLen,claimHigh⟩ := PV_RunJoin_ClaimCanonical41.encode ops claims extras
                                    rw [hclaim]
                                    try simp only [bind_tc_ok]
                                    obtain ⟨header25,framed25,hlen25,fb25,fp25⟩ :=
                                      PV_RunJoin_RecordFrame41.frame ops 25#u8 4#u8 3712#usize
                                        (alloc.vec.Vec.deref claimBytes) (PV_RunJoin_RowShapes41.row25 ops) claimLen (by scalar_tac)
                                    apply PV_RunJoin_RecordAppend41.bind_post fp25
                                    intro recorded25 hr25
                                    cases recorded25 with
                                    | Err error => trivial
                                    | Ok recordValue25 =>
                                      try simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok,lift,Aeneas.Std.uncurry,bind_assoc_eq]
                                      change recordValue25=framed25 at hr25
                                      subst recordValue25
                                      try simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok,lift,Aeneas.Std.uncurry,bind_assoc_eq]
                                      apply PV_RunJoin_ResultPost41.bind
                                      intro circle25
                                      rcases circle25 with ⟨circleResult25,t8⟩
                                      cases circleResult25 with
                                      | Err error => trivial
                                      | Ok z0 =>
                                        try simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok,lift,Aeneas.Std.uncurry,bind_assoc_eq]
                                        have fl25 : framed25.length=5+3712 := by
                                          change framed25.val.length=5+3712
                                          rw [fb25,List.length_append,hlen25]
                                          exact congrArg (fun n => 5+n) claimLen
                                        obtain ⟨b8,hext25,vext25⟩ := PV_RunJoin_ByteAppend38.append b7
                                          (alloc.vec.Vec.deref framed25)
                                          (by change b7.length+framed25.length≤Usize.max;rw [lb7,fl25];scalar_tac)
                                        rw [hext25]
                                        try simp only [bind_tc_ok]
                                        have piece25 : PV_RunJoin_CanonicalRecord43.Piece 3712 b7.val b8.val := by
                                          refine ⟨header25,claimBytes.val,hlen25,claimLen,claimHigh,?_⟩
                                          rw [vext25]
                                          change b7.val++framed25.val=b7.val++header25++claimBytes.val
                                          change framed25.val=header25++claimBytes.val at fb25
                                          rw [fb25,List.append_assoc]
                                        have lb8 : b8.length=12898 := by
                                          have h := PV_RunJoin_CanonicalRecord43.length piece25
                                          change b8.val.length=12898
                                          rw [show b7.val.length=9181 from lb7] at h
                                          exact h
                                        apply PV_RunJoin_RecordAppend41.bind_post (PV_RunJoin_EndpointCanonical41.post ops columns variant z0)
                                        intro endpointBytes ep
                                        obtain ⟨endpointLen,endpointHigh⟩ := ep
                                        obtain ⟨header26,framed26,hlen26,fb26,fp26⟩ :=
                                          PV_RunJoin_RecordFrame41.frame ops 26#u8 5#u8 928#usize
                                            (alloc.vec.Vec.deref endpointBytes) (PV_RunJoin_RowShapes41.row26 ops) endpointLen (by scalar_tac)
                                        apply PV_RunJoin_RecordAppend41.bind_post fp26
                                        intro recorded26 hr26
                                        cases recorded26 with
                                        | Err error => trivial
                                        | Ok recordValue26 =>
                                          try simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok,lift,Aeneas.Std.uncurry,bind_assoc_eq]
                                          change recordValue26=framed26 at hr26
                                          subst recordValue26
                                          try simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok,lift,Aeneas.Std.uncurry,bind_assoc_eq]
                                          apply PV_RunJoin_ResultPost41.bind
                                          intro circle26
                                          rcases circle26 with ⟨circleResult26,t9⟩
                                          cases circleResult26 with
                                          | Err error => trivial
                                          | Ok z1 =>
                                            try simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok,lift,Aeneas.Std.uncurry,bind_assoc_eq]
                                            have fl26 : framed26.length=5+928 := by
                                              change framed26.val.length=5+928
                                              rw [fb26,List.length_append,hlen26]
                                              exact congrArg (fun n => 5+n) endpointLen
                                            obtain ⟨b9,hext26,vext26⟩ := PV_RunJoin_ByteAppend38.append b8
                                              (alloc.vec.Vec.deref framed26)
                                              (by change b8.length+framed26.length≤Usize.max;rw [lb8,fl26];scalar_tac)
                                            rw [hext26]
                                            try simp only [bind_tc_ok]
                                            have piece26 : PV_RunJoin_CanonicalRecord43.Piece 928 b8.val b9.val := by
                                              refine ⟨header26,endpointBytes.val,hlen26,endpointLen,endpointHigh,?_⟩
                                              rw [vext26]
                                              change b8.val++framed26.val=b8.val++header26++endpointBytes.val
                                              change framed26.val=header26++endpointBytes.val at fb26
                                              rw [fb26,List.append_assoc]
                                            have lb9 : b9.length=13831 := by
                                              have h := PV_RunJoin_CanonicalRecord43.length piece26
                                              change b9.val.length=13831
                                              rw [show b8.val.length=12898 from lb8] at h
                                              exact h
                                            apply PV_RunJoin_ResultPost41.bind
                                            intro equalPoints
                                            cases equalPoints with
                                            | true => trivial
                                            | false =>
                                              exact ⟨lb9, PV_RunJoin_LayoutPieces43.domain ops (alloc.vec.Vec.deref b9)
                                                b5.val b6.val b7.val b8.val lb5 hm hs piece25 piece26⟩
#print axioms post
end R1Z.PV_RunJoin_CallerDomain43
