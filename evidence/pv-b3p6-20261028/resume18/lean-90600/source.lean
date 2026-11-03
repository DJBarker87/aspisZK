import PV_B3P_FixedIndex572227
namespace PV_B3P_FixedIndices572227_01
open Aeneas Aeneas.Std PV_B3P_PanicPatterns571227 PV_B3P_FixedIndex572227
set_option autoImplicit false
/-- Actual source instance 56:95965c546ae80dd61779, statement 29501. -/
def sourceState_32 : IndexState := ⟨1, 3⟩
theorem guard_32 : indexGuard sourceState_32 := fixed_guard 1 1
theorem certificate_32 {α : Type} (normal first second : Result α) :
    ¬ diagnostic (indexGuard sourceState_32) ∧
      branch (indexGuard sourceState_32) normal first =
        branch (indexGuard sourceState_32) normal second :=
  fixed_certificate 1 1 normal first second
#print axioms guard_32
#print axioms certificate_32
/-- Actual source instance 56:95965c546ae80dd61779, statement 29506. -/
def sourceState_33 : IndexState := ⟨2, 3⟩
theorem guard_33 : indexGuard sourceState_33 := fixed_guard 2 0
theorem certificate_33 {α : Type} (normal first second : Result α) :
    ¬ diagnostic (indexGuard sourceState_33) ∧
      branch (indexGuard sourceState_33) normal first =
        branch (indexGuard sourceState_33) normal second :=
  fixed_certificate 2 0 normal first second
#print axioms guard_33
#print axioms certificate_33
/-- Actual source instance 56:95965c546ae80dd61779, statement 29511. -/
def sourceState_34 : IndexState := ⟨10, 16⟩
theorem guard_34 : indexGuard sourceState_34 := fixed_guard 10 5
theorem certificate_34 {α : Type} (normal first second : Result α) :
    ¬ diagnostic (indexGuard sourceState_34) ∧
      branch (indexGuard sourceState_34) normal first =
        branch (indexGuard sourceState_34) normal second :=
  fixed_certificate 10 5 normal first second
#print axioms guard_34
#print axioms certificate_34
/-- Actual source instance 56:95965c546ae80dd61779, statement 29516. -/
def sourceState_35 : IndexState := ⟨30, 33⟩
theorem guard_35 : indexGuard sourceState_35 := fixed_guard 30 2
theorem certificate_35 {α : Type} (normal first second : Result α) :
    ¬ diagnostic (indexGuard sourceState_35) ∧
      branch (indexGuard sourceState_35) normal first =
        branch (indexGuard sourceState_35) normal second :=
  fixed_certificate 30 2 normal first second
#print axioms guard_35
#print axioms certificate_35
/-- Actual source instance 56:95965c546ae80dd61779, statement 29521. -/
def sourceState_36 : IndexState := ⟨10, 16⟩
theorem guard_36 : indexGuard sourceState_36 := fixed_guard 10 5
theorem certificate_36 {α : Type} (normal first second : Result α) :
    ¬ diagnostic (indexGuard sourceState_36) ∧
      branch (indexGuard sourceState_36) normal first =
        branch (indexGuard sourceState_36) normal second :=
  fixed_certificate 10 5 normal first second
#print axioms guard_36
#print axioms certificate_36
/-- Actual source instance 56:95965c546ae80dd61779, statement 29526. -/
def sourceState_37 : IndexState := ⟨31, 33⟩
theorem guard_37 : indexGuard sourceState_37 := fixed_guard 31 1
theorem certificate_37 {α : Type} (normal first second : Result α) :
    ¬ diagnostic (indexGuard sourceState_37) ∧
      branch (indexGuard sourceState_37) normal first =
        branch (indexGuard sourceState_37) normal second :=
  fixed_certificate 31 1 normal first second
#print axioms guard_37
#print axioms certificate_37
/-- Actual source instance 56:95965c546ae80dd61779, statement 29531. -/
def sourceState_38 : IndexState := ⟨10, 16⟩
theorem guard_38 : indexGuard sourceState_38 := fixed_guard 10 5
theorem certificate_38 {α : Type} (normal first second : Result α) :
    ¬ diagnostic (indexGuard sourceState_38) ∧
      branch (indexGuard sourceState_38) normal first =
        branch (indexGuard sourceState_38) normal second :=
  fixed_certificate 10 5 normal first second
#print axioms guard_38
#print axioms certificate_38
/-- Actual source instance 56:95965c546ae80dd61779, statement 29536. -/
def sourceState_39 : IndexState := ⟨32, 33⟩
theorem guard_39 : indexGuard sourceState_39 := fixed_guard 32 0
theorem certificate_39 {α : Type} (normal first second : Result α) :
    ¬ diagnostic (indexGuard sourceState_39) ∧
      branch (indexGuard sourceState_39) normal first =
        branch (indexGuard sourceState_39) normal second :=
  fixed_certificate 32 0 normal first second
#print axioms guard_39
#print axioms certificate_39
/-- Actual source instance 56:95965c546ae80dd61779, statement 29541. -/
def sourceState_40 : IndexState := ⟨0, 16⟩
theorem guard_40 : indexGuard sourceState_40 := fixed_guard 0 15
theorem certificate_40 {α : Type} (normal first second : Result α) :
    ¬ diagnostic (indexGuard sourceState_40) ∧
      branch (indexGuard sourceState_40) normal first =
        branch (indexGuard sourceState_40) normal second :=
  fixed_certificate 0 15 normal first second
#print axioms guard_40
#print axioms certificate_40
/-- Actual source instance 56:95965c546ae80dd61779, statement 29546. -/
def sourceState_41 : IndexState := ⟨1, 16⟩
theorem guard_41 : indexGuard sourceState_41 := fixed_guard 1 14
theorem certificate_41 {α : Type} (normal first second : Result α) :
    ¬ diagnostic (indexGuard sourceState_41) ∧
      branch (indexGuard sourceState_41) normal first =
        branch (indexGuard sourceState_41) normal second :=
  fixed_certificate 1 14 normal first second
#print axioms guard_41
#print axioms certificate_41
/-- Actual source instance 56:95965c546ae80dd61779, statement 29551. -/
def sourceState_42 : IndexState := ⟨2, 16⟩
theorem guard_42 : indexGuard sourceState_42 := fixed_guard 2 13
theorem certificate_42 {α : Type} (normal first second : Result α) :
    ¬ diagnostic (indexGuard sourceState_42) ∧
      branch (indexGuard sourceState_42) normal first =
        branch (indexGuard sourceState_42) normal second :=
  fixed_certificate 2 13 normal first second
#print axioms guard_42
#print axioms certificate_42
/-- Actual source instance 56:95965c546ae80dd61779, statement 29556. -/
def sourceState_43 : IndexState := ⟨0, 16⟩
theorem guard_43 : indexGuard sourceState_43 := fixed_guard 0 15
theorem certificate_43 {α : Type} (normal first second : Result α) :
    ¬ diagnostic (indexGuard sourceState_43) ∧
      branch (indexGuard sourceState_43) normal first =
        branch (indexGuard sourceState_43) normal second :=
  fixed_certificate 0 15 normal first second
#print axioms guard_43
#print axioms certificate_43
/-- Actual source instance 56:95965c546ae80dd61779, statement 29561. -/
def sourceState_44 : IndexState := ⟨1, 16⟩
theorem guard_44 : indexGuard sourceState_44 := fixed_guard 1 14
theorem certificate_44 {α : Type} (normal first second : Result α) :
    ¬ diagnostic (indexGuard sourceState_44) ∧
      branch (indexGuard sourceState_44) normal first =
        branch (indexGuard sourceState_44) normal second :=
  fixed_certificate 1 14 normal first second
#print axioms guard_44
#print axioms certificate_44
/-- Actual source instance 69:95965c546ae80dd61779, statement 29609. -/
def sourceState_45 : IndexState := ⟨0, 2⟩
theorem guard_45 : indexGuard sourceState_45 := fixed_guard 0 1
theorem certificate_45 {α : Type} (normal first second : Result α) :
    ¬ diagnostic (indexGuard sourceState_45) ∧
      branch (indexGuard sourceState_45) normal first =
        branch (indexGuard sourceState_45) normal second :=
  fixed_certificate 0 1 normal first second
#print axioms guard_45
#print axioms certificate_45
/-- Actual source instance 69:95965c546ae80dd61779, statement 29614. -/
def sourceState_46 : IndexState := ⟨1, 2⟩
theorem guard_46 : indexGuard sourceState_46 := fixed_guard 1 0
theorem certificate_46 {α : Type} (normal first second : Result α) :
    ¬ diagnostic (indexGuard sourceState_46) ∧
      branch (indexGuard sourceState_46) normal first =
        branch (indexGuard sourceState_46) normal second :=
  fixed_certificate 1 0 normal first second
#print axioms guard_46
#print axioms certificate_46
/-- Actual source instance 69:95965c546ae80dd61779, statement 29619. -/
def sourceState_47 : IndexState := ⟨0, 2⟩
theorem guard_47 : indexGuard sourceState_47 := fixed_guard 0 1
theorem certificate_47 {α : Type} (normal first second : Result α) :
    ¬ diagnostic (indexGuard sourceState_47) ∧
      branch (indexGuard sourceState_47) normal first =
        branch (indexGuard sourceState_47) normal second :=
  fixed_certificate 0 1 normal first second
#print axioms guard_47
#print axioms certificate_47
/-- Actual source instance 69:95965c546ae80dd61779, statement 29624. -/
def sourceState_48 : IndexState := ⟨1, 2⟩
theorem guard_48 : indexGuard sourceState_48 := fixed_guard 1 0
theorem certificate_48 {α : Type} (normal first second : Result α) :
    ¬ diagnostic (indexGuard sourceState_48) ∧
      branch (indexGuard sourceState_48) normal first =
        branch (indexGuard sourceState_48) normal second :=
  fixed_certificate 1 0 normal first second
#print axioms guard_48
#print axioms certificate_48
/-- Actual source instance 69:95965c546ae80dd61779, statement 29629. -/
def sourceState_49 : IndexState := ⟨0, 4⟩
theorem guard_49 : indexGuard sourceState_49 := fixed_guard 0 3
theorem certificate_49 {α : Type} (normal first second : Result α) :
    ¬ diagnostic (indexGuard sourceState_49) ∧
      branch (indexGuard sourceState_49) normal first =
        branch (indexGuard sourceState_49) normal second :=
  fixed_certificate 0 3 normal first second
#print axioms guard_49
#print axioms certificate_49
/-- Actual source instance 69:95965c546ae80dd61779, statement 29634. -/
def sourceState_50 : IndexState := ⟨1, 4⟩
theorem guard_50 : indexGuard sourceState_50 := fixed_guard 1 2
theorem certificate_50 {α : Type} (normal first second : Result α) :
    ¬ diagnostic (indexGuard sourceState_50) ∧
      branch (indexGuard sourceState_50) normal first =
        branch (indexGuard sourceState_50) normal second :=
  fixed_certificate 1 2 normal first second
#print axioms guard_50
#print axioms certificate_50
/-- Actual source instance 69:95965c546ae80dd61779, statement 29639. -/
def sourceState_51 : IndexState := ⟨2, 4⟩
theorem guard_51 : indexGuard sourceState_51 := fixed_guard 2 1
theorem certificate_51 {α : Type} (normal first second : Result α) :
    ¬ diagnostic (indexGuard sourceState_51) ∧
      branch (indexGuard sourceState_51) normal first =
        branch (indexGuard sourceState_51) normal second :=
  fixed_certificate 2 1 normal first second
#print axioms guard_51
#print axioms certificate_51
/-- Actual source instance 69:95965c546ae80dd61779, statement 29644. -/
def sourceState_52 : IndexState := ⟨3, 4⟩
theorem guard_52 : indexGuard sourceState_52 := fixed_guard 3 0
theorem certificate_52 {α : Type} (normal first second : Result α) :
    ¬ diagnostic (indexGuard sourceState_52) ∧
      branch (indexGuard sourceState_52) normal first =
        branch (indexGuard sourceState_52) normal second :=
  fixed_certificate 3 0 normal first second
#print axioms guard_52
#print axioms certificate_52
/-- Actual source instance 69:95965c546ae80dd61779, statement 29649. -/
def sourceState_53 : IndexState := ⟨0, 2⟩
theorem guard_53 : indexGuard sourceState_53 := fixed_guard 0 1
theorem certificate_53 {α : Type} (normal first second : Result α) :
    ¬ diagnostic (indexGuard sourceState_53) ∧
      branch (indexGuard sourceState_53) normal first =
        branch (indexGuard sourceState_53) normal second :=
  fixed_certificate 0 1 normal first second
#print axioms guard_53
#print axioms certificate_53
/-- Actual source instance 69:95965c546ae80dd61779, statement 29654. -/
def sourceState_54 : IndexState := ⟨1, 4⟩
theorem guard_54 : indexGuard sourceState_54 := fixed_guard 1 2
theorem certificate_54 {α : Type} (normal first second : Result α) :
    ¬ diagnostic (indexGuard sourceState_54) ∧
      branch (indexGuard sourceState_54) normal first =
        branch (indexGuard sourceState_54) normal second :=
  fixed_certificate 1 2 normal first second
#print axioms guard_54
#print axioms certificate_54
/-- Actual source instance 69:95965c546ae80dd61779, statement 29659. -/
def sourceState_55 : IndexState := ⟨1, 2⟩
theorem guard_55 : indexGuard sourceState_55 := fixed_guard 1 0
theorem certificate_55 {α : Type} (normal first second : Result α) :
    ¬ diagnostic (indexGuard sourceState_55) ∧
      branch (indexGuard sourceState_55) normal first =
        branch (indexGuard sourceState_55) normal second :=
  fixed_certificate 1 0 normal first second
#print axioms guard_55
#print axioms certificate_55
/-- Actual source instance 69:95965c546ae80dd61779, statement 29664. -/
def sourceState_56 : IndexState := ⟨0, 4⟩
theorem guard_56 : indexGuard sourceState_56 := fixed_guard 0 3
theorem certificate_56 {α : Type} (normal first second : Result α) :
    ¬ diagnostic (indexGuard sourceState_56) ∧
      branch (indexGuard sourceState_56) normal first =
        branch (indexGuard sourceState_56) normal second :=
  fixed_certificate 0 3 normal first second
#print axioms guard_56
#print axioms certificate_56
/-- Actual source instance 69:95965c546ae80dd61779, statement 29669. -/
def sourceState_57 : IndexState := ⟨0, 2⟩
theorem guard_57 : indexGuard sourceState_57 := fixed_guard 0 1
theorem certificate_57 {α : Type} (normal first second : Result α) :
    ¬ diagnostic (indexGuard sourceState_57) ∧
      branch (indexGuard sourceState_57) normal first =
        branch (indexGuard sourceState_57) normal second :=
  fixed_certificate 0 1 normal first second
#print axioms guard_57
#print axioms certificate_57
/-- Actual source instance 69:95965c546ae80dd61779, statement 29674. -/
def sourceState_58 : IndexState := ⟨3, 4⟩
theorem guard_58 : indexGuard sourceState_58 := fixed_guard 3 0
theorem certificate_58 {α : Type} (normal first second : Result α) :
    ¬ diagnostic (indexGuard sourceState_58) ∧
      branch (indexGuard sourceState_58) normal first =
        branch (indexGuard sourceState_58) normal second :=
  fixed_certificate 3 0 normal first second
#print axioms guard_58
#print axioms certificate_58
/-- Actual source instance 69:95965c546ae80dd61779, statement 29679. -/
def sourceState_59 : IndexState := ⟨1, 2⟩
theorem guard_59 : indexGuard sourceState_59 := fixed_guard 1 0
theorem certificate_59 {α : Type} (normal first second : Result α) :
    ¬ diagnostic (indexGuard sourceState_59) ∧
      branch (indexGuard sourceState_59) normal first =
        branch (indexGuard sourceState_59) normal second :=
  fixed_certificate 1 0 normal first second
#print axioms guard_59
#print axioms certificate_59
/-- Actual source instance 69:95965c546ae80dd61779, statement 29684. -/
def sourceState_60 : IndexState := ⟨2, 4⟩
theorem guard_60 : indexGuard sourceState_60 := fixed_guard 2 1
theorem certificate_60 {α : Type} (normal first second : Result α) :
    ¬ diagnostic (indexGuard sourceState_60) ∧
      branch (indexGuard sourceState_60) normal first =
        branch (indexGuard sourceState_60) normal second :=
  fixed_certificate 2 1 normal first second
#print axioms guard_60
#print axioms certificate_60
/-- Actual source instance 72:95965c546ae80dd61779, statement 29714. -/
def sourceState_61 : IndexState := ⟨0, 3⟩
theorem guard_61 : indexGuard sourceState_61 := fixed_guard 0 2
theorem certificate_61 {α : Type} (normal first second : Result α) :
    ¬ diagnostic (indexGuard sourceState_61) ∧
      branch (indexGuard sourceState_61) normal first =
        branch (indexGuard sourceState_61) normal second :=
  fixed_certificate 0 2 normal first second
#print axioms guard_61
#print axioms certificate_61
/-- Actual source instance 72:95965c546ae80dd61779, statement 29719. -/
def sourceState_62 : IndexState := ⟨1, 3⟩
theorem guard_62 : indexGuard sourceState_62 := fixed_guard 1 1
theorem certificate_62 {α : Type} (normal first second : Result α) :
    ¬ diagnostic (indexGuard sourceState_62) ∧
      branch (indexGuard sourceState_62) normal first =
        branch (indexGuard sourceState_62) normal second :=
  fixed_certificate 1 1 normal first second
#print axioms guard_62
#print axioms certificate_62
/-- Actual source instance 72:95965c546ae80dd61779, statement 29724. -/
def sourceState_63 : IndexState := ⟨2, 3⟩
theorem guard_63 : indexGuard sourceState_63 := fixed_guard 2 0
theorem certificate_63 {α : Type} (normal first second : Result α) :
    ¬ diagnostic (indexGuard sourceState_63) ∧
      branch (indexGuard sourceState_63) normal first =
        branch (indexGuard sourceState_63) normal second :=
  fixed_certificate 2 0 normal first second
#print axioms guard_63
#print axioms certificate_63
end PV_B3P_FixedIndices572227_01
