import R1Z.ProverRwOrderedQuerySource
import R1Z.ProverRwOrderedBounds
set_option autoImplicit false
namespace R1Z.ProverRwOrderedQueryBounds
open Aeneas Aeneas.Std Result ProverRwFull
open ProverRwOrderedOracle ProverRwOrderedBounds
variable [ExternalTypes] [ExternalFuns]
theorem absorb {H : Type} (hash : aspis_core.digest.Digest32 H)
    (self : host_transcript.Transcript H) (row : U8) (payload : Slice U8) :
    (ProverRwOrderedQuerySource.absorb hash self row payload).history.length≤1 := by
  unfold ProverRwOrderedQuerySource.absorb
  apply bind_bound (n:=0) (m:=1)
  · exact native_bound _
  · intro v0
    apply bind_bound (n:=0) (m:=1)
    · exact native_bound _
    · intro v1
      apply bind_bound (n:=0) (m:=1)
      · exact native_bound _
      · intro v2
        apply bind_bound (n:=0) (m:=1)
        · exact native_bound _
        · intro v3
          apply bind_bound (n:=0) (m:=1)
          · exact native_bound _
          · intro v4
            apply bind_bound (n:=0) (m:=1)
            · exact native_bound _
            · intro v5
              apply bind_bound (n:=0) (m:=1)
              · exact native_bound _
              · intro v6
                apply bind_bound (n:=1) (m:=0)
                · exact query_bound _ _
                · intro v7
                  exact pure_bound _
#print axioms absorb


theorem materializeK {H : Type} (hash : aspis_core.digest.Digest32 H)
    (self : host_transcript.Transcript H) (row : U8) (payload : Slice U8) :
    (ProverRwOrderedQuerySource.materialize hash self row payload).history.length≤17 := by
  unfold ProverRwOrderedQuerySource.materialize ProverRwOrderedQuerySource.materializeK
  apply bind_bound (n:=1) (m:=16)
  · exact absorb _ _ _ _
  · intro v0
    apply bind_bound (n:=0) (m:=16)
    · exact native_bound _
    · intro v1
      apply bind_bound (n:=0) (m:=16)
      · exact native_bound _
      · intro v2
        apply bind_bound (n:=0) (m:=16)
        · exact native_bound _
        · intro v3
          apply bind_bound (n:=1) (m:=15)
          · exact query_bound _ _
          · intro v4
            apply bind_bound (n:=0) (m:=15)
            · exact native_bound _
            · intro v5
              apply bind_bound (n:=0) (m:=15)
              · exact native_bound _
              · intro v6
                apply bind_bound (n:=0) (m:=15)
                · exact native_bound _
                · intro v7
                  apply bind_bound (n:=0) (m:=15)
                  · exact native_bound _
                  · intro v8
                    apply bind_bound (n:=1) (m:=14)
                    · exact query_bound _ _
                    · intro v9
                      apply bind_bound (n:=0) (m:=14)
                      · exact native_bound _
                      · intro v10
                        apply bind_bound (n:=0) (m:=14)
                        · exact native_bound _
                        · intro v11
                          apply bind_bound (n:=0) (m:=14)
                          · exact native_bound _
                          · intro v12
                            apply bind_bound (n:=0) (m:=14)
                            · exact native_bound _
                            · intro v13
                              apply bind_bound (n:=1) (m:=13)
                              · exact query_bound _ _
                              · intro v14
                                apply bind_bound (n:=0) (m:=13)
                                · exact native_bound _
                                · intro v15
                                  apply bind_bound (n:=0) (m:=13)
                                  · exact native_bound _
                                  · intro v16
                                    apply bind_bound (n:=0) (m:=13)
                                    · exact native_bound _
                                    · intro v17
                                      apply bind_bound (n:=0) (m:=13)
                                      · exact native_bound _
                                      · intro v18
                                        apply bind_bound (n:=1) (m:=12)
                                        · exact query_bound _ _
                                        · intro v19
                                          apply bind_bound (n:=0) (m:=12)
                                          · exact native_bound _
                                          · intro v20
                                            apply bind_bound (n:=0) (m:=12)
                                            · exact native_bound _
                                            · intro v21
                                              apply bind_bound (n:=0) (m:=12)
                                              · exact native_bound _
                                              · intro v22
                                                apply bind_bound (n:=0) (m:=12)
                                                · exact native_bound _
                                                · intro v23
                                                  apply bind_bound (n:=0) (m:=12)
                                                  · exact native_bound _
                                                  · intro v24
                                                    apply bind_bound (n:=1) (m:=11)
                                                    · exact query_bound _ _
                                                    · intro v25
                                                      apply bind_bound (n:=0) (m:=11)
                                                      · exact native_bound _
                                                      · intro v26
                                                        apply bind_bound (n:=0) (m:=11)
                                                        · exact native_bound _
                                                        · intro v27
                                                          apply bind_bound (n:=0) (m:=11)
                                                          · exact native_bound _
                                                          · intro v28
                                                            apply bind_bound (n:=0) (m:=11)
                                                            · exact native_bound _
                                                            · intro v29
                                                              apply bind_bound (n:=1) (m:=10)
                                                              · exact query_bound _ _
                                                              · intro v30
                                                                apply bind_bound (n:=0) (m:=10)
                                                                · exact native_bound _
                                                                · intro v31
                                                                  apply bind_bound (n:=0) (m:=10)
                                                                  · exact native_bound _
                                                                  · intro v32
                                                                    apply bind_bound (n:=0) (m:=10)
                                                                    · exact native_bound _
                                                                    · intro v33
                                                                      apply bind_bound (n:=0) (m:=10)
                                                                      · exact native_bound _
                                                                      · intro v34
                                                                        apply bind_bound (n:=0) (m:=10)
                                                                        · exact native_bound _
                                                                        · intro v35
                                                                          apply bind_bound (n:=1) (m:=9)
                                                                          · exact query_bound _ _
                                                                          · intro v36
                                                                            apply bind_bound (n:=0) (m:=9)
                                                                            · exact native_bound _
                                                                            · intro v37
                                                                              apply bind_bound (n:=0) (m:=9)
                                                                              · exact native_bound _
                                                                              · intro v38
                                                                                apply bind_bound (n:=0) (m:=9)
                                                                                · exact native_bound _
                                                                                · intro v39
                                                                                  apply bind_bound (n:=0) (m:=9)
                                                                                  · exact native_bound _
                                                                                  · intro v40
                                                                                    apply bind_bound (n:=1) (m:=8)
                                                                                    · exact query_bound _ _
                                                                                    · intro v41
                                                                                      apply bind_bound (n:=0) (m:=8)
                                                                                      · exact native_bound _
                                                                                      · intro v42
                                                                                        apply bind_bound (n:=0) (m:=8)
                                                                                        · exact native_bound _
                                                                                        · intro v43
                                                                                          apply bind_bound (n:=0) (m:=8)
                                                                                          · exact native_bound _
                                                                                          · intro v44
                                                                                            apply bind_bound (n:=0) (m:=8)
                                                                                            · exact native_bound _
                                                                                            · intro v45
                                                                                              apply bind_bound (n:=0) (m:=8)
                                                                                              · exact native_bound _
                                                                                              · intro v46
                                                                                                apply bind_bound (n:=1) (m:=7)
                                                                                                · exact query_bound _ _
                                                                                                · intro v47
                                                                                                  apply bind_bound (n:=0) (m:=7)
                                                                                                  · exact native_bound _
                                                                                                  · intro v48
                                                                                                    apply bind_bound (n:=0) (m:=7)
                                                                                                    · exact native_bound _
                                                                                                    · intro v49
                                                                                                      apply bind_bound (n:=0) (m:=7)
                                                                                                      · exact native_bound _
                                                                                                      · intro v50
                                                                                                        apply bind_bound (n:=0) (m:=7)
                                                                                                        · exact native_bound _
                                                                                                        · intro v51
                                                                                                          apply bind_bound (n:=1) (m:=6)
                                                                                                          · exact query_bound _ _
                                                                                                          · intro v52
                                                                                                            apply bind_bound (n:=0) (m:=6)
                                                                                                            · exact native_bound _
                                                                                                            · intro v53
                                                                                                              apply bind_bound (n:=0) (m:=6)
                                                                                                              · exact native_bound _
                                                                                                              · intro v54
                                                                                                                apply bind_bound (n:=0) (m:=6)
                                                                                                                · exact native_bound _
                                                                                                                · intro v55
                                                                                                                  apply bind_bound (n:=0) (m:=6)
                                                                                                                  · exact native_bound _
                                                                                                                  · intro v56
                                                                                                                    apply bind_bound (n:=0) (m:=6)
                                                                                                                    · exact native_bound _
                                                                                                                    · intro v57
                                                                                                                      apply bind_bound (n:=1) (m:=5)
                                                                                                                      · exact query_bound _ _
                                                                                                                      · intro v58
                                                                                                                        apply bind_bound (n:=0) (m:=5)
                                                                                                                        · exact native_bound _
                                                                                                                        · intro v59
                                                                                                                          apply bind_bound (n:=0) (m:=5)
                                                                                                                          · exact native_bound _
                                                                                                                          · intro v60
                                                                                                                            apply bind_bound (n:=0) (m:=5)
                                                                                                                            · exact native_bound _
                                                                                                                            · intro v61
                                                                                                                              apply bind_bound (n:=0) (m:=5)
                                                                                                                              · exact native_bound _
                                                                                                                              · intro v62
                                                                                                                                apply bind_bound (n:=1) (m:=4)
                                                                                                                                · exact query_bound _ _
                                                                                                                                · intro v63
                                                                                                                                  apply bind_bound (n:=0) (m:=4)
                                                                                                                                  · exact native_bound _
                                                                                                                                  · intro v64
                                                                                                                                    apply bind_bound (n:=0) (m:=4)
                                                                                                                                    · exact native_bound _
                                                                                                                                    · intro v65
                                                                                                                                      apply bind_bound (n:=0) (m:=4)
                                                                                                                                      · exact native_bound _
                                                                                                                                      · intro v66
                                                                                                                                        apply bind_bound (n:=0) (m:=4)
                                                                                                                                        · exact native_bound _
                                                                                                                                        · intro v67
                                                                                                                                          apply bind_bound (n:=0) (m:=4)
                                                                                                                                          · exact native_bound _
                                                                                                                                          · intro v68
                                                                                                                                            apply bind_bound (n:=1) (m:=3)
                                                                                                                                            · exact query_bound _ _
                                                                                                                                            · intro v69
                                                                                                                                              apply bind_bound (n:=0) (m:=3)
                                                                                                                                              · exact native_bound _
                                                                                                                                              · intro v70
                                                                                                                                                apply bind_bound (n:=0) (m:=3)
                                                                                                                                                · exact native_bound _
                                                                                                                                                · intro v71
                                                                                                                                                  apply bind_bound (n:=0) (m:=3)
                                                                                                                                                  · exact native_bound _
                                                                                                                                                  · intro v72
                                                                                                                                                    apply bind_bound (n:=0) (m:=3)
                                                                                                                                                    · exact native_bound _
                                                                                                                                                    · intro v73
                                                                                                                                                      apply bind_bound (n:=1) (m:=2)
                                                                                                                                                      · exact query_bound _ _
                                                                                                                                                      · intro v74
                                                                                                                                                        apply bind_bound (n:=0) (m:=2)
                                                                                                                                                        · exact native_bound _
                                                                                                                                                        · intro v75
                                                                                                                                                          apply bind_bound (n:=0) (m:=2)
                                                                                                                                                          · exact native_bound _
                                                                                                                                                          · intro v76
                                                                                                                                                            apply bind_bound (n:=0) (m:=2)
                                                                                                                                                            · exact native_bound _
                                                                                                                                                            · intro v77
                                                                                                                                                              apply bind_bound (n:=0) (m:=2)
                                                                                                                                                              · exact native_bound _
                                                                                                                                                              · intro v78
                                                                                                                                                                apply bind_bound (n:=0) (m:=2)
                                                                                                                                                                · exact native_bound _
                                                                                                                                                                · intro v79
                                                                                                                                                                  apply bind_bound (n:=1) (m:=1)
                                                                                                                                                                  · exact query_bound _ _
                                                                                                                                                                  · intro v80
                                                                                                                                                                    apply bind_bound (n:=0) (m:=1)
                                                                                                                                                                    · exact native_bound _
                                                                                                                                                                    · intro v81
                                                                                                                                                                      apply bind_bound (n:=0) (m:=1)
                                                                                                                                                                      · exact native_bound _
                                                                                                                                                                      · intro v82
                                                                                                                                                                        apply bind_bound (n:=0) (m:=1)
                                                                                                                                                                        · exact native_bound _
                                                                                                                                                                        · intro v83
                                                                                                                                                                          apply bind_bound (n:=0) (m:=1)
                                                                                                                                                                          · exact native_bound _
                                                                                                                                                                          · intro v84
                                                                                                                                                                            apply bind_bound (n:=1) (m:=0)
                                                                                                                                                                            · exact query_bound _ _
                                                                                                                                                                            · intro v85
                                                                                                                                                                              apply bind_bound (n:=0) (m:=0)
                                                                                                                                                                              · exact native_bound _
                                                                                                                                                                              · intro v86
                                                                                                                                                                                apply bind_bound (n:=0) (m:=0)
                                                                                                                                                                                · exact native_bound _
                                                                                                                                                                                · intro v87
                                                                                                                                                                                  exact pure_bound _
#print axioms materializeK

end R1Z.ProverRwOrderedQueryBounds
