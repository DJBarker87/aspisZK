import PV_B3P_FixedIndex572227
namespace PV_B3P_FixedIndices572227_00
open Aeneas Aeneas.Std PV_B3P_PanicPatterns571227 PV_B3P_FixedIndex572227
set_option autoImplicit false
/-- Actual source instance 9:95965c546ae80dd61779, statement 29239. -/
def sourceState_0 : IndexState := ⟨0, 10⟩
theorem guard_0 : indexGuard sourceState_0 := fixed_guard 0 9
theorem certificate_0 {α : Type} (normal first second : Result α) :
    ¬ diagnostic (indexGuard sourceState_0) ∧
      branch (indexGuard sourceState_0) normal first =
        branch (indexGuard sourceState_0) normal second :=
  fixed_certificate 0 9 normal first second
#print axioms guard_0
#print axioms certificate_0
/-- Actual source instance 9:95965c546ae80dd61779, statement 29244. -/
def sourceState_1 : IndexState := ⟨0, 10⟩
theorem guard_1 : indexGuard sourceState_1 := fixed_guard 0 9
theorem certificate_1 {α : Type} (normal first second : Result α) :
    ¬ diagnostic (indexGuard sourceState_1) ∧
      branch (indexGuard sourceState_1) normal first =
        branch (indexGuard sourceState_1) normal second :=
  fixed_certificate 0 9 normal first second
#print axioms guard_1
#print axioms certificate_1
/-- Actual source instance 18:95965c546ae80dd61779, statement 29265. -/
def sourceState_2 : IndexState := ⟨0, 16⟩
theorem guard_2 : indexGuard sourceState_2 := fixed_guard 0 15
theorem certificate_2 {α : Type} (normal first second : Result α) :
    ¬ diagnostic (indexGuard sourceState_2) ∧
      branch (indexGuard sourceState_2) normal first =
        branch (indexGuard sourceState_2) normal second :=
  fixed_certificate 0 15 normal first second
#print axioms guard_2
#print axioms certificate_2
/-- Actual source instance 19:95965c546ae80dd61779, statement 29271. -/
def sourceState_3 : IndexState := ⟨1, 16⟩
theorem guard_3 : indexGuard sourceState_3 := fixed_guard 1 14
theorem certificate_3 {α : Type} (normal first second : Result α) :
    ¬ diagnostic (indexGuard sourceState_3) ∧
      branch (indexGuard sourceState_3) normal first =
        branch (indexGuard sourceState_3) normal second :=
  fixed_certificate 1 14 normal first second
#print axioms guard_3
#print axioms certificate_3
/-- Actual source instance 19:95965c546ae80dd61779, statement 29276. -/
def sourceState_4 : IndexState := ⟨10, 16⟩
theorem guard_4 : indexGuard sourceState_4 := fixed_guard 10 5
theorem certificate_4 {α : Type} (normal first second : Result α) :
    ¬ diagnostic (indexGuard sourceState_4) ∧
      branch (indexGuard sourceState_4) normal first =
        branch (indexGuard sourceState_4) normal second :=
  fixed_certificate 10 5 normal first second
#print axioms guard_4
#print axioms certificate_4
/-- Actual source instance 24:95965c546ae80dd61779, statement 29290. -/
def sourceState_5 : IndexState := ⟨0, 3⟩
theorem guard_5 : indexGuard sourceState_5 := fixed_guard 0 2
theorem certificate_5 {α : Type} (normal first second : Result α) :
    ¬ diagnostic (indexGuard sourceState_5) ∧
      branch (indexGuard sourceState_5) normal first =
        branch (indexGuard sourceState_5) normal second :=
  fixed_certificate 0 2 normal first second
#print axioms guard_5
#print axioms certificate_5
/-- Actual source instance 24:95965c546ae80dd61779, statement 29295. -/
def sourceState_6 : IndexState := ⟨1, 3⟩
theorem guard_6 : indexGuard sourceState_6 := fixed_guard 1 1
theorem certificate_6 {α : Type} (normal first second : Result α) :
    ¬ diagnostic (indexGuard sourceState_6) ∧
      branch (indexGuard sourceState_6) normal first =
        branch (indexGuard sourceState_6) normal second :=
  fixed_certificate 1 1 normal first second
#print axioms guard_6
#print axioms certificate_6
/-- Actual source instance 24:95965c546ae80dd61779, statement 29300. -/
def sourceState_7 : IndexState := ⟨2, 3⟩
theorem guard_7 : indexGuard sourceState_7 := fixed_guard 2 0
theorem certificate_7 {α : Type} (normal first second : Result α) :
    ¬ diagnostic (indexGuard sourceState_7) ∧
      branch (indexGuard sourceState_7) normal first =
        branch (indexGuard sourceState_7) normal second :=
  fixed_certificate 2 0 normal first second
#print axioms guard_7
#print axioms certificate_7
/-- Actual source instance 39:95965c546ae80dd61779, statement 29310. -/
def sourceState_8 : IndexState := ⟨0, 8⟩
theorem guard_8 : indexGuard sourceState_8 := fixed_guard 0 7
theorem certificate_8 {α : Type} (normal first second : Result α) :
    ¬ diagnostic (indexGuard sourceState_8) ∧
      branch (indexGuard sourceState_8) normal first =
        branch (indexGuard sourceState_8) normal second :=
  fixed_certificate 0 7 normal first second
#print axioms guard_8
#print axioms certificate_8
/-- Actual source instance 39:95965c546ae80dd61779, statement 29315. -/
def sourceState_9 : IndexState := ⟨1, 8⟩
theorem guard_9 : indexGuard sourceState_9 := fixed_guard 1 6
theorem certificate_9 {α : Type} (normal first second : Result α) :
    ¬ diagnostic (indexGuard sourceState_9) ∧
      branch (indexGuard sourceState_9) normal first =
        branch (indexGuard sourceState_9) normal second :=
  fixed_certificate 1 6 normal first second
#print axioms guard_9
#print axioms certificate_9
/-- Actual source instance 39:95965c546ae80dd61779, statement 29320. -/
def sourceState_10 : IndexState := ⟨2, 8⟩
theorem guard_10 : indexGuard sourceState_10 := fixed_guard 2 5
theorem certificate_10 {α : Type} (normal first second : Result α) :
    ¬ diagnostic (indexGuard sourceState_10) ∧
      branch (indexGuard sourceState_10) normal first =
        branch (indexGuard sourceState_10) normal second :=
  fixed_certificate 2 5 normal first second
#print axioms guard_10
#print axioms certificate_10
/-- Actual source instance 39:95965c546ae80dd61779, statement 29325. -/
def sourceState_11 : IndexState := ⟨3, 8⟩
theorem guard_11 : indexGuard sourceState_11 := fixed_guard 3 4
theorem certificate_11 {α : Type} (normal first second : Result α) :
    ¬ diagnostic (indexGuard sourceState_11) ∧
      branch (indexGuard sourceState_11) normal first =
        branch (indexGuard sourceState_11) normal second :=
  fixed_certificate 3 4 normal first second
#print axioms guard_11
#print axioms certificate_11
/-- Actual source instance 39:95965c546ae80dd61779, statement 29330. -/
def sourceState_12 : IndexState := ⟨4, 8⟩
theorem guard_12 : indexGuard sourceState_12 := fixed_guard 4 3
theorem certificate_12 {α : Type} (normal first second : Result α) :
    ¬ diagnostic (indexGuard sourceState_12) ∧
      branch (indexGuard sourceState_12) normal first =
        branch (indexGuard sourceState_12) normal second :=
  fixed_certificate 4 3 normal first second
#print axioms guard_12
#print axioms certificate_12
/-- Actual source instance 39:95965c546ae80dd61779, statement 29335. -/
def sourceState_13 : IndexState := ⟨5, 8⟩
theorem guard_13 : indexGuard sourceState_13 := fixed_guard 5 2
theorem certificate_13 {α : Type} (normal first second : Result α) :
    ¬ diagnostic (indexGuard sourceState_13) ∧
      branch (indexGuard sourceState_13) normal first =
        branch (indexGuard sourceState_13) normal second :=
  fixed_certificate 5 2 normal first second
#print axioms guard_13
#print axioms certificate_13
/-- Actual source instance 39:95965c546ae80dd61779, statement 29340. -/
def sourceState_14 : IndexState := ⟨6, 8⟩
theorem guard_14 : indexGuard sourceState_14 := fixed_guard 6 1
theorem certificate_14 {α : Type} (normal first second : Result α) :
    ¬ diagnostic (indexGuard sourceState_14) ∧
      branch (indexGuard sourceState_14) normal first =
        branch (indexGuard sourceState_14) normal second :=
  fixed_certificate 6 1 normal first second
#print axioms guard_14
#print axioms certificate_14
/-- Actual source instance 39:95965c546ae80dd61779, statement 29345. -/
def sourceState_15 : IndexState := ⟨7, 8⟩
theorem guard_15 : indexGuard sourceState_15 := fixed_guard 7 0
theorem certificate_15 {α : Type} (normal first second : Result α) :
    ¬ diagnostic (indexGuard sourceState_15) ∧
      branch (indexGuard sourceState_15) normal first =
        branch (indexGuard sourceState_15) normal second :=
  fixed_certificate 7 0 normal first second
#print axioms guard_15
#print axioms certificate_15
/-- Actual source instance 48:95965c546ae80dd61779, statement 29370. -/
def sourceState_16 : IndexState := ⟨0, 4⟩
theorem guard_16 : indexGuard sourceState_16 := fixed_guard 0 3
theorem certificate_16 {α : Type} (normal first second : Result α) :
    ¬ diagnostic (indexGuard sourceState_16) ∧
      branch (indexGuard sourceState_16) normal first =
        branch (indexGuard sourceState_16) normal second :=
  fixed_certificate 0 3 normal first second
#print axioms guard_16
#print axioms certificate_16
/-- Actual source instance 48:95965c546ae80dd61779, statement 29375. -/
def sourceState_17 : IndexState := ⟨1, 4⟩
theorem guard_17 : indexGuard sourceState_17 := fixed_guard 1 2
theorem certificate_17 {α : Type} (normal first second : Result α) :
    ¬ diagnostic (indexGuard sourceState_17) ∧
      branch (indexGuard sourceState_17) normal first =
        branch (indexGuard sourceState_17) normal second :=
  fixed_certificate 1 2 normal first second
#print axioms guard_17
#print axioms certificate_17
/-- Actual source instance 49:95965c546ae80dd61779, statement 29380. -/
def sourceState_18 : IndexState := ⟨1, 16⟩
theorem guard_18 : indexGuard sourceState_18 := fixed_guard 1 14
theorem certificate_18 {α : Type} (normal first second : Result α) :
    ¬ diagnostic (indexGuard sourceState_18) ∧
      branch (indexGuard sourceState_18) normal first =
        branch (indexGuard sourceState_18) normal second :=
  fixed_certificate 1 14 normal first second
#print axioms guard_18
#print axioms certificate_18
/-- Actual source instance 49:95965c546ae80dd61779, statement 29385. -/
def sourceState_19 : IndexState := ⟨9, 16⟩
theorem guard_19 : indexGuard sourceState_19 := fixed_guard 9 6
theorem certificate_19 {α : Type} (normal first second : Result α) :
    ¬ diagnostic (indexGuard sourceState_19) ∧
      branch (indexGuard sourceState_19) normal first =
        branch (indexGuard sourceState_19) normal second :=
  fixed_certificate 9 6 normal first second
#print axioms guard_19
#print axioms certificate_19
/-- Actual source instance 49:95965c546ae80dd61779, statement 29390. -/
def sourceState_20 : IndexState := ⟨10, 16⟩
theorem guard_20 : indexGuard sourceState_20 := fixed_guard 10 5
theorem certificate_20 {α : Type} (normal first second : Result α) :
    ¬ diagnostic (indexGuard sourceState_20) ∧
      branch (indexGuard sourceState_20) normal first =
        branch (indexGuard sourceState_20) normal second :=
  fixed_certificate 10 5 normal first second
#print axioms guard_20
#print axioms certificate_20
/-- Actual source instance 49:95965c546ae80dd61779, statement 29395. -/
def sourceState_21 : IndexState := ⟨2, 4⟩
theorem guard_21 : indexGuard sourceState_21 := fixed_guard 2 1
theorem certificate_21 {α : Type} (normal first second : Result α) :
    ¬ diagnostic (indexGuard sourceState_21) ∧
      branch (indexGuard sourceState_21) normal first =
        branch (indexGuard sourceState_21) normal second :=
  fixed_certificate 2 1 normal first second
#print axioms guard_21
#print axioms certificate_21
/-- Actual source instance 49:95965c546ae80dd61779, statement 29400. -/
def sourceState_22 : IndexState := ⟨0, 4⟩
theorem guard_22 : indexGuard sourceState_22 := fixed_guard 0 3
theorem certificate_22 {α : Type} (normal first second : Result α) :
    ¬ diagnostic (indexGuard sourceState_22) ∧
      branch (indexGuard sourceState_22) normal first =
        branch (indexGuard sourceState_22) normal second :=
  fixed_certificate 0 3 normal first second
#print axioms guard_22
#print axioms certificate_22
/-- Actual source instance 49:95965c546ae80dd61779, statement 29405. -/
def sourceState_23 : IndexState := ⟨2, 4⟩
theorem guard_23 : indexGuard sourceState_23 := fixed_guard 2 1
theorem certificate_23 {α : Type} (normal first second : Result α) :
    ¬ diagnostic (indexGuard sourceState_23) ∧
      branch (indexGuard sourceState_23) normal first =
        branch (indexGuard sourceState_23) normal second :=
  fixed_certificate 2 1 normal first second
#print axioms guard_23
#print axioms certificate_23
/-- Actual source instance 49:95965c546ae80dd61779, statement 29410. -/
def sourceState_24 : IndexState := ⟨3, 4⟩
theorem guard_24 : indexGuard sourceState_24 := fixed_guard 3 0
theorem certificate_24 {α : Type} (normal first second : Result α) :
    ¬ diagnostic (indexGuard sourceState_24) ∧
      branch (indexGuard sourceState_24) normal first =
        branch (indexGuard sourceState_24) normal second :=
  fixed_certificate 3 0 normal first second
#print axioms guard_24
#print axioms certificate_24
/-- Actual source instance 49:95965c546ae80dd61779, statement 29415. -/
def sourceState_25 : IndexState := ⟨1, 4⟩
theorem guard_25 : indexGuard sourceState_25 := fixed_guard 1 2
theorem certificate_25 {α : Type} (normal first second : Result α) :
    ¬ diagnostic (indexGuard sourceState_25) ∧
      branch (indexGuard sourceState_25) normal first =
        branch (indexGuard sourceState_25) normal second :=
  fixed_certificate 1 2 normal first second
#print axioms guard_25
#print axioms certificate_25
/-- Actual source instance 49:95965c546ae80dd61779, statement 29420. -/
def sourceState_26 : IndexState := ⟨3, 4⟩
theorem guard_26 : indexGuard sourceState_26 := fixed_guard 3 0
theorem certificate_26 {α : Type} (normal first second : Result α) :
    ¬ diagnostic (indexGuard sourceState_26) ∧
      branch (indexGuard sourceState_26) normal first =
        branch (indexGuard sourceState_26) normal second :=
  fixed_certificate 3 0 normal first second
#print axioms guard_26
#print axioms certificate_26
/-- Actual source instance 55:95965c546ae80dd61779, statement 29430. -/
def sourceState_27 : IndexState := ⟨1, 16⟩
theorem guard_27 : indexGuard sourceState_27 := fixed_guard 1 14
theorem certificate_27 {α : Type} (normal first second : Result α) :
    ¬ diagnostic (indexGuard sourceState_27) ∧
      branch (indexGuard sourceState_27) normal first =
        branch (indexGuard sourceState_27) normal second :=
  fixed_certificate 1 14 normal first second
#print axioms guard_27
#print axioms certificate_27
/-- Actual source instance 55:95965c546ae80dd61779, statement 29435. -/
def sourceState_28 : IndexState := ⟨5, 16⟩
theorem guard_28 : indexGuard sourceState_28 := fixed_guard 5 10
theorem certificate_28 {α : Type} (normal first second : Result α) :
    ¬ diagnostic (indexGuard sourceState_28) ∧
      branch (indexGuard sourceState_28) normal first =
        branch (indexGuard sourceState_28) normal second :=
  fixed_certificate 5 10 normal first second
#print axioms guard_28
#print axioms certificate_28
/-- Actual source instance 55:95965c546ae80dd61779, statement 29440. -/
def sourceState_29 : IndexState := ⟨9, 16⟩
theorem guard_29 : indexGuard sourceState_29 := fixed_guard 9 6
theorem certificate_29 {α : Type} (normal first second : Result α) :
    ¬ diagnostic (indexGuard sourceState_29) ∧
      branch (indexGuard sourceState_29) normal first =
        branch (indexGuard sourceState_29) normal second :=
  fixed_certificate 9 6 normal first second
#print axioms guard_29
#print axioms certificate_29
/-- Actual source instance 55:95965c546ae80dd61779, statement 29445. -/
def sourceState_30 : IndexState := ⟨13, 16⟩
theorem guard_30 : indexGuard sourceState_30 := fixed_guard 13 2
theorem certificate_30 {α : Type} (normal first second : Result α) :
    ¬ diagnostic (indexGuard sourceState_30) ∧
      branch (indexGuard sourceState_30) normal first =
        branch (indexGuard sourceState_30) normal second :=
  fixed_certificate 13 2 normal first second
#print axioms guard_30
#print axioms certificate_30
/-- Actual source instance 56:95965c546ae80dd61779, statement 29496. -/
def sourceState_31 : IndexState := ⟨0, 3⟩
theorem guard_31 : indexGuard sourceState_31 := fixed_guard 0 2
theorem certificate_31 {α : Type} (normal first second : Result α) :
    ¬ diagnostic (indexGuard sourceState_31) ∧
      branch (indexGuard sourceState_31) normal first =
        branch (indexGuard sourceState_31) normal second :=
  fixed_certificate 0 2 normal first second
#print axioms guard_31
#print axioms certificate_31
end PV_B3P_FixedIndices572227_00
