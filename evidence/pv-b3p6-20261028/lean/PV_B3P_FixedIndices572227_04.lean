import PV_B3P_FixedIndex572227
namespace PV_B3P_FixedIndices572227_04
open Aeneas Aeneas.Std PV_B3P_PanicPatterns571227 PV_B3P_FixedIndex572227
set_option autoImplicit false
/-- Actual source instance 239:95965c546ae80dd61779, statement 30438. -/
def sourceState_128 : IndexState := ⟨1, 12⟩
theorem guard_128 : indexGuard sourceState_128 := fixed_guard 1 10
theorem certificate_128 {α : Type} (normal first second : Result α) :
    ¬ diagnostic (indexGuard sourceState_128) ∧
      branch (indexGuard sourceState_128) normal first =
        branch (indexGuard sourceState_128) normal second :=
  fixed_certificate 1 10 normal first second
#print axioms guard_128
#print axioms certificate_128
/-- Actual source instance 239:95965c546ae80dd61779, statement 30443. -/
def sourceState_129 : IndexState := ⟨2, 12⟩
theorem guard_129 : indexGuard sourceState_129 := fixed_guard 2 9
theorem certificate_129 {α : Type} (normal first second : Result α) :
    ¬ diagnostic (indexGuard sourceState_129) ∧
      branch (indexGuard sourceState_129) normal first =
        branch (indexGuard sourceState_129) normal second :=
  fixed_certificate 2 9 normal first second
#print axioms guard_129
#print axioms certificate_129
/-- Actual source instance 239:95965c546ae80dd61779, statement 30448. -/
def sourceState_130 : IndexState := ⟨10, 16⟩
theorem guard_130 : indexGuard sourceState_130 := fixed_guard 10 5
theorem certificate_130 {α : Type} (normal first second : Result α) :
    ¬ diagnostic (indexGuard sourceState_130) ∧
      branch (indexGuard sourceState_130) normal first =
        branch (indexGuard sourceState_130) normal second :=
  fixed_certificate 10 5 normal first second
#print axioms guard_130
#print axioms certificate_130
/-- Actual source instance 239:95965c546ae80dd61779, statement 30453. -/
def sourceState_131 : IndexState := ⟨11, 12⟩
theorem guard_131 : indexGuard sourceState_131 := fixed_guard 11 0
theorem certificate_131 {α : Type} (normal first second : Result α) :
    ¬ diagnostic (indexGuard sourceState_131) ∧
      branch (indexGuard sourceState_131) normal first =
        branch (indexGuard sourceState_131) normal second :=
  fixed_certificate 11 0 normal first second
#print axioms guard_131
#print axioms certificate_131
/-- Actual source instance 241:95965c546ae80dd61779, statement 30489. -/
def sourceState_132 : IndexState := ⟨0, 4⟩
theorem guard_132 : indexGuard sourceState_132 := fixed_guard 0 3
theorem certificate_132 {α : Type} (normal first second : Result α) :
    ¬ diagnostic (indexGuard sourceState_132) ∧
      branch (indexGuard sourceState_132) normal first =
        branch (indexGuard sourceState_132) normal second :=
  fixed_certificate 0 3 normal first second
#print axioms guard_132
#print axioms certificate_132
/-- Actual source instance 241:95965c546ae80dd61779, statement 30494. -/
def sourceState_133 : IndexState := ⟨1, 4⟩
theorem guard_133 : indexGuard sourceState_133 := fixed_guard 1 2
theorem certificate_133 {α : Type} (normal first second : Result α) :
    ¬ diagnostic (indexGuard sourceState_133) ∧
      branch (indexGuard sourceState_133) normal first =
        branch (indexGuard sourceState_133) normal second :=
  fixed_certificate 1 2 normal first second
#print axioms guard_133
#print axioms certificate_133
/-- Actual source instance 241:95965c546ae80dd61779, statement 30499. -/
def sourceState_134 : IndexState := ⟨2, 4⟩
theorem guard_134 : indexGuard sourceState_134 := fixed_guard 2 1
theorem certificate_134 {α : Type} (normal first second : Result α) :
    ¬ diagnostic (indexGuard sourceState_134) ∧
      branch (indexGuard sourceState_134) normal first =
        branch (indexGuard sourceState_134) normal second :=
  fixed_certificate 2 1 normal first second
#print axioms guard_134
#print axioms certificate_134
/-- Actual source instance 241:95965c546ae80dd61779, statement 30504. -/
def sourceState_135 : IndexState := ⟨3, 4⟩
theorem guard_135 : indexGuard sourceState_135 := fixed_guard 3 0
theorem certificate_135 {α : Type} (normal first second : Result α) :
    ¬ diagnostic (indexGuard sourceState_135) ∧
      branch (indexGuard sourceState_135) normal first =
        branch (indexGuard sourceState_135) normal second :=
  fixed_certificate 3 0 normal first second
#print axioms guard_135
#print axioms certificate_135
/-- Actual source instance 343:95965c546ae80dd61779, statement 30699. -/
def sourceState_136 : IndexState := ⟨0, 4⟩
theorem guard_136 : indexGuard sourceState_136 := fixed_guard 0 3
theorem certificate_136 {α : Type} (normal first second : Result α) :
    ¬ diagnostic (indexGuard sourceState_136) ∧
      branch (indexGuard sourceState_136) normal first =
        branch (indexGuard sourceState_136) normal second :=
  fixed_certificate 0 3 normal first second
#print axioms guard_136
#print axioms certificate_136
/-- Actual source instance 343:95965c546ae80dd61779, statement 30704. -/
def sourceState_137 : IndexState := ⟨1, 4⟩
theorem guard_137 : indexGuard sourceState_137 := fixed_guard 1 2
theorem certificate_137 {α : Type} (normal first second : Result α) :
    ¬ diagnostic (indexGuard sourceState_137) ∧
      branch (indexGuard sourceState_137) normal first =
        branch (indexGuard sourceState_137) normal second :=
  fixed_certificate 1 2 normal first second
#print axioms guard_137
#print axioms certificate_137
/-- Actual source instance 343:95965c546ae80dd61779, statement 30709. -/
def sourceState_138 : IndexState := ⟨2, 4⟩
theorem guard_138 : indexGuard sourceState_138 := fixed_guard 2 1
theorem certificate_138 {α : Type} (normal first second : Result α) :
    ¬ diagnostic (indexGuard sourceState_138) ∧
      branch (indexGuard sourceState_138) normal first =
        branch (indexGuard sourceState_138) normal second :=
  fixed_certificate 2 1 normal first second
#print axioms guard_138
#print axioms certificate_138
/-- Actual source instance 343:95965c546ae80dd61779, statement 30714. -/
def sourceState_139 : IndexState := ⟨3, 4⟩
theorem guard_139 : indexGuard sourceState_139 := fixed_guard 3 0
theorem certificate_139 {α : Type} (normal first second : Result α) :
    ¬ diagnostic (indexGuard sourceState_139) ∧
      branch (indexGuard sourceState_139) normal first =
        branch (indexGuard sourceState_139) normal second :=
  fixed_certificate 3 0 normal first second
#print axioms guard_139
#print axioms certificate_139
/-- Actual source instance 346:95965c546ae80dd61779, statement 30745. -/
def sourceState_140 : IndexState := ⟨0, 4⟩
theorem guard_140 : indexGuard sourceState_140 := fixed_guard 0 3
theorem certificate_140 {α : Type} (normal first second : Result α) :
    ¬ diagnostic (indexGuard sourceState_140) ∧
      branch (indexGuard sourceState_140) normal first =
        branch (indexGuard sourceState_140) normal second :=
  fixed_certificate 0 3 normal first second
#print axioms guard_140
#print axioms certificate_140
/-- Actual source instance 346:95965c546ae80dd61779, statement 30750. -/
def sourceState_141 : IndexState := ⟨1, 4⟩
theorem guard_141 : indexGuard sourceState_141 := fixed_guard 1 2
theorem certificate_141 {α : Type} (normal first second : Result α) :
    ¬ diagnostic (indexGuard sourceState_141) ∧
      branch (indexGuard sourceState_141) normal first =
        branch (indexGuard sourceState_141) normal second :=
  fixed_certificate 1 2 normal first second
#print axioms guard_141
#print axioms certificate_141
/-- Actual source instance 346:95965c546ae80dd61779, statement 30755. -/
def sourceState_142 : IndexState := ⟨2, 4⟩
theorem guard_142 : indexGuard sourceState_142 := fixed_guard 2 1
theorem certificate_142 {α : Type} (normal first second : Result α) :
    ¬ diagnostic (indexGuard sourceState_142) ∧
      branch (indexGuard sourceState_142) normal first =
        branch (indexGuard sourceState_142) normal second :=
  fixed_certificate 2 1 normal first second
#print axioms guard_142
#print axioms certificate_142
/-- Actual source instance 346:95965c546ae80dd61779, statement 30760. -/
def sourceState_143 : IndexState := ⟨3, 4⟩
theorem guard_143 : indexGuard sourceState_143 := fixed_guard 3 0
theorem certificate_143 {α : Type} (normal first second : Result α) :
    ¬ diagnostic (indexGuard sourceState_143) ∧
      branch (indexGuard sourceState_143) normal first =
        branch (indexGuard sourceState_143) normal second :=
  fixed_certificate 3 0 normal first second
#print axioms guard_143
#print axioms certificate_143
/-- Actual source instance 362:95965c546ae80dd61779, statement 30811. -/
def sourceState_144 : IndexState := ⟨0, 16⟩
theorem guard_144 : indexGuard sourceState_144 := fixed_guard 0 15
theorem certificate_144 {α : Type} (normal first second : Result α) :
    ¬ diagnostic (indexGuard sourceState_144) ∧
      branch (indexGuard sourceState_144) normal first =
        branch (indexGuard sourceState_144) normal second :=
  fixed_certificate 0 15 normal first second
#print axioms guard_144
#print axioms certificate_144
/-- Actual source instance 362:95965c546ae80dd61779, statement 30816. -/
def sourceState_145 : IndexState := ⟨0, 16⟩
theorem guard_145 : indexGuard sourceState_145 := fixed_guard 0 15
theorem certificate_145 {α : Type} (normal first second : Result α) :
    ¬ diagnostic (indexGuard sourceState_145) ∧
      branch (indexGuard sourceState_145) normal first =
        branch (indexGuard sourceState_145) normal second :=
  fixed_certificate 0 15 normal first second
#print axioms guard_145
#print axioms certificate_145
/-- Actual source instance 494:95965c546ae80dd61779, statement 30978. -/
def sourceState_146 : IndexState := ⟨0, 4⟩
theorem guard_146 : indexGuard sourceState_146 := fixed_guard 0 3
theorem certificate_146 {α : Type} (normal first second : Result α) :
    ¬ diagnostic (indexGuard sourceState_146) ∧
      branch (indexGuard sourceState_146) normal first =
        branch (indexGuard sourceState_146) normal second :=
  fixed_certificate 0 3 normal first second
#print axioms guard_146
#print axioms certificate_146
/-- Actual source instance 494:95965c546ae80dd61779, statement 30988. -/
def sourceState_147 : IndexState := ⟨1, 4⟩
theorem guard_147 : indexGuard sourceState_147 := fixed_guard 1 2
theorem certificate_147 {α : Type} (normal first second : Result α) :
    ¬ diagnostic (indexGuard sourceState_147) ∧
      branch (indexGuard sourceState_147) normal first =
        branch (indexGuard sourceState_147) normal second :=
  fixed_certificate 1 2 normal first second
#print axioms guard_147
#print axioms certificate_147
/-- Actual source instance 494:95965c546ae80dd61779, statement 30998. -/
def sourceState_148 : IndexState := ⟨2, 4⟩
theorem guard_148 : indexGuard sourceState_148 := fixed_guard 2 1
theorem certificate_148 {α : Type} (normal first second : Result α) :
    ¬ diagnostic (indexGuard sourceState_148) ∧
      branch (indexGuard sourceState_148) normal first =
        branch (indexGuard sourceState_148) normal second :=
  fixed_certificate 2 1 normal first second
#print axioms guard_148
#print axioms certificate_148
/-- Actual source instance 494:95965c546ae80dd61779, statement 31008. -/
def sourceState_149 : IndexState := ⟨2, 4⟩
theorem guard_149 : indexGuard sourceState_149 := fixed_guard 2 1
theorem certificate_149 {α : Type} (normal first second : Result α) :
    ¬ diagnostic (indexGuard sourceState_149) ∧
      branch (indexGuard sourceState_149) normal first =
        branch (indexGuard sourceState_149) normal second :=
  fixed_certificate 2 1 normal first second
#print axioms guard_149
#print axioms certificate_149
/-- Actual source instance 494:95965c546ae80dd61779, statement 31018. -/
def sourceState_150 : IndexState := ⟨3, 4⟩
theorem guard_150 : indexGuard sourceState_150 := fixed_guard 3 0
theorem certificate_150 {α : Type} (normal first second : Result α) :
    ¬ diagnostic (indexGuard sourceState_150) ∧
      branch (indexGuard sourceState_150) normal first =
        branch (indexGuard sourceState_150) normal second :=
  fixed_certificate 3 0 normal first second
#print axioms guard_150
#print axioms certificate_150
/-- Actual source instance 494:95965c546ae80dd61779, statement 31028. -/
def sourceState_151 : IndexState := ⟨3, 4⟩
theorem guard_151 : indexGuard sourceState_151 := fixed_guard 3 0
theorem certificate_151 {α : Type} (normal first second : Result α) :
    ¬ diagnostic (indexGuard sourceState_151) ∧
      branch (indexGuard sourceState_151) normal first =
        branch (indexGuard sourceState_151) normal second :=
  fixed_certificate 3 0 normal first second
#print axioms guard_151
#print axioms certificate_151
/-- Actual source instance 494:95965c546ae80dd61779, statement 31038. -/
def sourceState_152 : IndexState := ⟨0, 4⟩
theorem guard_152 : indexGuard sourceState_152 := fixed_guard 0 3
theorem certificate_152 {α : Type} (normal first second : Result α) :
    ¬ diagnostic (indexGuard sourceState_152) ∧
      branch (indexGuard sourceState_152) normal first =
        branch (indexGuard sourceState_152) normal second :=
  fixed_certificate 0 3 normal first second
#print axioms guard_152
#print axioms certificate_152
/-- Actual source instance 494:95965c546ae80dd61779, statement 31048. -/
def sourceState_153 : IndexState := ⟨1, 4⟩
theorem guard_153 : indexGuard sourceState_153 := fixed_guard 1 2
theorem certificate_153 {α : Type} (normal first second : Result α) :
    ¬ diagnostic (indexGuard sourceState_153) ∧
      branch (indexGuard sourceState_153) normal first =
        branch (indexGuard sourceState_153) normal second :=
  fixed_certificate 1 2 normal first second
#print axioms guard_153
#print axioms certificate_153
/-- Actual source instance 494:95965c546ae80dd61779, statement 31058. -/
def sourceState_154 : IndexState := ⟨2, 4⟩
theorem guard_154 : indexGuard sourceState_154 := fixed_guard 2 1
theorem certificate_154 {α : Type} (normal first second : Result α) :
    ¬ diagnostic (indexGuard sourceState_154) ∧
      branch (indexGuard sourceState_154) normal first =
        branch (indexGuard sourceState_154) normal second :=
  fixed_certificate 2 1 normal first second
#print axioms guard_154
#print axioms certificate_154
/-- Actual source instance 494:95965c546ae80dd61779, statement 31068. -/
def sourceState_155 : IndexState := ⟨2, 4⟩
theorem guard_155 : indexGuard sourceState_155 := fixed_guard 2 1
theorem certificate_155 {α : Type} (normal first second : Result α) :
    ¬ diagnostic (indexGuard sourceState_155) ∧
      branch (indexGuard sourceState_155) normal first =
        branch (indexGuard sourceState_155) normal second :=
  fixed_certificate 2 1 normal first second
#print axioms guard_155
#print axioms certificate_155
/-- Actual source instance 494:95965c546ae80dd61779, statement 31078. -/
def sourceState_156 : IndexState := ⟨3, 4⟩
theorem guard_156 : indexGuard sourceState_156 := fixed_guard 3 0
theorem certificate_156 {α : Type} (normal first second : Result α) :
    ¬ diagnostic (indexGuard sourceState_156) ∧
      branch (indexGuard sourceState_156) normal first =
        branch (indexGuard sourceState_156) normal second :=
  fixed_certificate 3 0 normal first second
#print axioms guard_156
#print axioms certificate_156
/-- Actual source instance 494:95965c546ae80dd61779, statement 31088. -/
def sourceState_157 : IndexState := ⟨3, 4⟩
theorem guard_157 : indexGuard sourceState_157 := fixed_guard 3 0
theorem certificate_157 {α : Type} (normal first second : Result α) :
    ¬ diagnostic (indexGuard sourceState_157) ∧
      branch (indexGuard sourceState_157) normal first =
        branch (indexGuard sourceState_157) normal second :=
  fixed_certificate 3 0 normal first second
#print axioms guard_157
#print axioms certificate_157
/-- Actual source instance 494:95965c546ae80dd61779, statement 31098. -/
def sourceState_158 : IndexState := ⟨0, 4⟩
theorem guard_158 : indexGuard sourceState_158 := fixed_guard 0 3
theorem certificate_158 {α : Type} (normal first second : Result α) :
    ¬ diagnostic (indexGuard sourceState_158) ∧
      branch (indexGuard sourceState_158) normal first =
        branch (indexGuard sourceState_158) normal second :=
  fixed_certificate 0 3 normal first second
#print axioms guard_158
#print axioms certificate_158
/-- Actual source instance 494:95965c546ae80dd61779, statement 31108. -/
def sourceState_159 : IndexState := ⟨1, 4⟩
theorem guard_159 : indexGuard sourceState_159 := fixed_guard 1 2
theorem certificate_159 {α : Type} (normal first second : Result α) :
    ¬ diagnostic (indexGuard sourceState_159) ∧
      branch (indexGuard sourceState_159) normal first =
        branch (indexGuard sourceState_159) normal second :=
  fixed_certificate 1 2 normal first second
#print axioms guard_159
#print axioms certificate_159
end PV_B3P_FixedIndices572227_04
