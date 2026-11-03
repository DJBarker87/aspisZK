import PV_B3P_FixedIndex572227
namespace PV_B3P_FixedIndices572227_05
open Aeneas Aeneas.Std PV_B3P_PanicPatterns571227 PV_B3P_FixedIndex572227
set_option autoImplicit false
/-- Actual source instance 494:95965c546ae80dd61779, statement 31118. -/
def sourceState_160 : IndexState := ⟨2, 4⟩
theorem guard_160 : indexGuard sourceState_160 := fixed_guard 2 1
theorem certificate_160 {α : Type} (normal first second : Result α) :
    ¬ diagnostic (indexGuard sourceState_160) ∧
      branch (indexGuard sourceState_160) normal first =
        branch (indexGuard sourceState_160) normal second :=
  fixed_certificate 2 1 normal first second
#print axioms guard_160
#print axioms certificate_160
/-- Actual source instance 494:95965c546ae80dd61779, statement 31128. -/
def sourceState_161 : IndexState := ⟨3, 4⟩
theorem guard_161 : indexGuard sourceState_161 := fixed_guard 3 0
theorem certificate_161 {α : Type} (normal first second : Result α) :
    ¬ diagnostic (indexGuard sourceState_161) ∧
      branch (indexGuard sourceState_161) normal first =
        branch (indexGuard sourceState_161) normal second :=
  fixed_certificate 3 0 normal first second
#print axioms guard_161
#print axioms certificate_161
/-- Actual source instance 494:95965c546ae80dd61779, statement 31138. -/
def sourceState_162 : IndexState := ⟨0, 4⟩
theorem guard_162 : indexGuard sourceState_162 := fixed_guard 0 3
theorem certificate_162 {α : Type} (normal first second : Result α) :
    ¬ diagnostic (indexGuard sourceState_162) ∧
      branch (indexGuard sourceState_162) normal first =
        branch (indexGuard sourceState_162) normal second :=
  fixed_certificate 0 3 normal first second
#print axioms guard_162
#print axioms certificate_162
/-- Actual source instance 494:95965c546ae80dd61779, statement 31148. -/
def sourceState_163 : IndexState := ⟨1, 4⟩
theorem guard_163 : indexGuard sourceState_163 := fixed_guard 1 2
theorem certificate_163 {α : Type} (normal first second : Result α) :
    ¬ diagnostic (indexGuard sourceState_163) ∧
      branch (indexGuard sourceState_163) normal first =
        branch (indexGuard sourceState_163) normal second :=
  fixed_certificate 1 2 normal first second
#print axioms guard_163
#print axioms certificate_163
/-- Actual source instance 494:95965c546ae80dd61779, statement 31158. -/
def sourceState_164 : IndexState := ⟨2, 4⟩
theorem guard_164 : indexGuard sourceState_164 := fixed_guard 2 1
theorem certificate_164 {α : Type} (normal first second : Result α) :
    ¬ diagnostic (indexGuard sourceState_164) ∧
      branch (indexGuard sourceState_164) normal first =
        branch (indexGuard sourceState_164) normal second :=
  fixed_certificate 2 1 normal first second
#print axioms guard_164
#print axioms certificate_164
/-- Actual source instance 494:95965c546ae80dd61779, statement 31168. -/
def sourceState_165 : IndexState := ⟨3, 4⟩
theorem guard_165 : indexGuard sourceState_165 := fixed_guard 3 0
theorem certificate_165 {α : Type} (normal first second : Result α) :
    ¬ diagnostic (indexGuard sourceState_165) ∧
      branch (indexGuard sourceState_165) normal first =
        branch (indexGuard sourceState_165) normal second :=
  fixed_certificate 3 0 normal first second
#print axioms guard_165
#print axioms certificate_165
/-- Actual source instance 494:95965c546ae80dd61779, statement 30958. -/
def sourceState_166 : IndexState := ⟨0, 4⟩
theorem guard_166 : indexGuard sourceState_166 := fixed_guard 0 3
theorem certificate_166 {α : Type} (normal first second : Result α) :
    ¬ diagnostic (indexGuard sourceState_166) ∧
      branch (indexGuard sourceState_166) normal first =
        branch (indexGuard sourceState_166) normal second :=
  fixed_certificate 0 3 normal first second
#print axioms guard_166
#print axioms certificate_166
/-- Actual source instance 494:95965c546ae80dd61779, statement 30963. -/
def sourceState_167 : IndexState := ⟨1, 4⟩
theorem guard_167 : indexGuard sourceState_167 := fixed_guard 1 2
theorem certificate_167 {α : Type} (normal first second : Result α) :
    ¬ diagnostic (indexGuard sourceState_167) ∧
      branch (indexGuard sourceState_167) normal first =
        branch (indexGuard sourceState_167) normal second :=
  fixed_certificate 1 2 normal first second
#print axioms guard_167
#print axioms certificate_167
/-- Actual source instance 494:95965c546ae80dd61779, statement 30968. -/
def sourceState_168 : IndexState := ⟨2, 4⟩
theorem guard_168 : indexGuard sourceState_168 := fixed_guard 2 1
theorem certificate_168 {α : Type} (normal first second : Result α) :
    ¬ diagnostic (indexGuard sourceState_168) ∧
      branch (indexGuard sourceState_168) normal first =
        branch (indexGuard sourceState_168) normal second :=
  fixed_certificate 2 1 normal first second
#print axioms guard_168
#print axioms certificate_168
/-- Actual source instance 494:95965c546ae80dd61779, statement 30973. -/
def sourceState_169 : IndexState := ⟨3, 4⟩
theorem guard_169 : indexGuard sourceState_169 := fixed_guard 3 0
theorem certificate_169 {α : Type} (normal first second : Result α) :
    ¬ diagnostic (indexGuard sourceState_169) ∧
      branch (indexGuard sourceState_169) normal first =
        branch (indexGuard sourceState_169) normal second :=
  fixed_certificate 3 0 normal first second
#print axioms guard_169
#print axioms certificate_169
/-- Actual source instance 319:95965c546ae80dd61779, statement 30562. -/
def sourceState_170 : IndexState := ⟨0, 4⟩
theorem guard_170 : indexGuard sourceState_170 := fixed_guard 0 3
theorem certificate_170 {α : Type} (normal first second : Result α) :
    ¬ diagnostic (indexGuard sourceState_170) ∧
      branch (indexGuard sourceState_170) normal first =
        branch (indexGuard sourceState_170) normal second :=
  fixed_certificate 0 3 normal first second
#print axioms guard_170
#print axioms certificate_170
/-- Actual source instance 319:95965c546ae80dd61779, statement 30567. -/
def sourceState_171 : IndexState := ⟨1, 4⟩
theorem guard_171 : indexGuard sourceState_171 := fixed_guard 1 2
theorem certificate_171 {α : Type} (normal first second : Result α) :
    ¬ diagnostic (indexGuard sourceState_171) ∧
      branch (indexGuard sourceState_171) normal first =
        branch (indexGuard sourceState_171) normal second :=
  fixed_certificate 1 2 normal first second
#print axioms guard_171
#print axioms certificate_171
/-- Actual source instance 319:95965c546ae80dd61779, statement 30572. -/
def sourceState_172 : IndexState := ⟨2, 4⟩
theorem guard_172 : indexGuard sourceState_172 := fixed_guard 2 1
theorem certificate_172 {α : Type} (normal first second : Result α) :
    ¬ diagnostic (indexGuard sourceState_172) ∧
      branch (indexGuard sourceState_172) normal first =
        branch (indexGuard sourceState_172) normal second :=
  fixed_certificate 2 1 normal first second
#print axioms guard_172
#print axioms certificate_172
/-- Actual source instance 319:95965c546ae80dd61779, statement 30577. -/
def sourceState_173 : IndexState := ⟨3, 4⟩
theorem guard_173 : indexGuard sourceState_173 := fixed_guard 3 0
theorem certificate_173 {α : Type} (normal first second : Result α) :
    ¬ diagnostic (indexGuard sourceState_173) ∧
      branch (indexGuard sourceState_173) normal first =
        branch (indexGuard sourceState_173) normal second :=
  fixed_certificate 3 0 normal first second
#print axioms guard_173
#print axioms certificate_173
/-- Actual source instance 321:95965c546ae80dd61779, statement 30679. -/
def sourceState_174 : IndexState := ⟨0, 3⟩
theorem guard_174 : indexGuard sourceState_174 := fixed_guard 0 2
theorem certificate_174 {α : Type} (normal first second : Result α) :
    ¬ diagnostic (indexGuard sourceState_174) ∧
      branch (indexGuard sourceState_174) normal first =
        branch (indexGuard sourceState_174) normal second :=
  fixed_certificate 0 2 normal first second
#print axioms guard_174
#print axioms certificate_174
/-- Actual source instance 321:95965c546ae80dd61779, statement 30684. -/
def sourceState_175 : IndexState := ⟨1, 3⟩
theorem guard_175 : indexGuard sourceState_175 := fixed_guard 1 1
theorem certificate_175 {α : Type} (normal first second : Result α) :
    ¬ diagnostic (indexGuard sourceState_175) ∧
      branch (indexGuard sourceState_175) normal first =
        branch (indexGuard sourceState_175) normal second :=
  fixed_certificate 1 1 normal first second
#print axioms guard_175
#print axioms certificate_175
/-- Actual source instance 321:95965c546ae80dd61779, statement 30689. -/
def sourceState_176 : IndexState := ⟨2, 3⟩
theorem guard_176 : indexGuard sourceState_176 := fixed_guard 2 0
theorem certificate_176 {α : Type} (normal first second : Result α) :
    ¬ diagnostic (indexGuard sourceState_176) ∧
      branch (indexGuard sourceState_176) normal first =
        branch (indexGuard sourceState_176) normal second :=
  fixed_certificate 2 0 normal first second
#print axioms guard_176
#print axioms certificate_176
/-- Actual source instance 428:95965c546ae80dd61779, statement 30863. -/
def sourceState_177 : IndexState := ⟨0, 4⟩
theorem guard_177 : indexGuard sourceState_177 := fixed_guard 0 3
theorem certificate_177 {α : Type} (normal first second : Result α) :
    ¬ diagnostic (indexGuard sourceState_177) ∧
      branch (indexGuard sourceState_177) normal first =
        branch (indexGuard sourceState_177) normal second :=
  fixed_certificate 0 3 normal first second
#print axioms guard_177
#print axioms certificate_177
/-- Actual source instance 428:95965c546ae80dd61779, statement 30873. -/
def sourceState_178 : IndexState := ⟨1, 4⟩
theorem guard_178 : indexGuard sourceState_178 := fixed_guard 1 2
theorem certificate_178 {α : Type} (normal first second : Result α) :
    ¬ diagnostic (indexGuard sourceState_178) ∧
      branch (indexGuard sourceState_178) normal first =
        branch (indexGuard sourceState_178) normal second :=
  fixed_certificate 1 2 normal first second
#print axioms guard_178
#print axioms certificate_178
/-- Actual source instance 428:95965c546ae80dd61779, statement 30883. -/
def sourceState_179 : IndexState := ⟨2, 4⟩
theorem guard_179 : indexGuard sourceState_179 := fixed_guard 2 1
theorem certificate_179 {α : Type} (normal first second : Result α) :
    ¬ diagnostic (indexGuard sourceState_179) ∧
      branch (indexGuard sourceState_179) normal first =
        branch (indexGuard sourceState_179) normal second :=
  fixed_certificate 2 1 normal first second
#print axioms guard_179
#print axioms certificate_179
/-- Actual source instance 428:95965c546ae80dd61779, statement 30893. -/
def sourceState_180 : IndexState := ⟨3, 4⟩
theorem guard_180 : indexGuard sourceState_180 := fixed_guard 3 0
theorem certificate_180 {α : Type} (normal first second : Result α) :
    ¬ diagnostic (indexGuard sourceState_180) ∧
      branch (indexGuard sourceState_180) normal first =
        branch (indexGuard sourceState_180) normal second :=
  fixed_certificate 3 0 normal first second
#print axioms guard_180
#print axioms certificate_180
/-- Actual source instance 424:95965c546ae80dd61779, statement 30848. -/
def sourceState_181 : IndexState := ⟨0, 3⟩
theorem guard_181 : indexGuard sourceState_181 := fixed_guard 0 2
theorem certificate_181 {α : Type} (normal first second : Result α) :
    ¬ diagnostic (indexGuard sourceState_181) ∧
      branch (indexGuard sourceState_181) normal first =
        branch (indexGuard sourceState_181) normal second :=
  fixed_certificate 0 2 normal first second
#print axioms guard_181
#print axioms certificate_181
/-- Actual source instance 424:95965c546ae80dd61779, statement 30853. -/
def sourceState_182 : IndexState := ⟨1, 3⟩
theorem guard_182 : indexGuard sourceState_182 := fixed_guard 1 1
theorem certificate_182 {α : Type} (normal first second : Result α) :
    ¬ diagnostic (indexGuard sourceState_182) ∧
      branch (indexGuard sourceState_182) normal first =
        branch (indexGuard sourceState_182) normal second :=
  fixed_certificate 1 1 normal first second
#print axioms guard_182
#print axioms certificate_182
/-- Actual source instance 424:95965c546ae80dd61779, statement 30858. -/
def sourceState_183 : IndexState := ⟨2, 3⟩
theorem guard_183 : indexGuard sourceState_183 := fixed_guard 2 0
theorem certificate_183 {α : Type} (normal first second : Result α) :
    ¬ diagnostic (indexGuard sourceState_183) ∧
      branch (indexGuard sourceState_183) normal first =
        branch (indexGuard sourceState_183) normal second :=
  fixed_certificate 2 0 normal first second
#print axioms guard_183
#print axioms certificate_183
/-- Actual source instance 484:95965c546ae80dd61779, statement 30933. -/
def sourceState_184 : IndexState := ⟨0, 3⟩
theorem guard_184 : indexGuard sourceState_184 := fixed_guard 0 2
theorem certificate_184 {α : Type} (normal first second : Result α) :
    ¬ diagnostic (indexGuard sourceState_184) ∧
      branch (indexGuard sourceState_184) normal first =
        branch (indexGuard sourceState_184) normal second :=
  fixed_certificate 0 2 normal first second
#print axioms guard_184
#print axioms certificate_184
/-- Actual source instance 484:95965c546ae80dd61779, statement 30938. -/
def sourceState_185 : IndexState := ⟨1, 3⟩
theorem guard_185 : indexGuard sourceState_185 := fixed_guard 1 1
theorem certificate_185 {α : Type} (normal first second : Result α) :
    ¬ diagnostic (indexGuard sourceState_185) ∧
      branch (indexGuard sourceState_185) normal first =
        branch (indexGuard sourceState_185) normal second :=
  fixed_certificate 1 1 normal first second
#print axioms guard_185
#print axioms certificate_185
/-- Actual source instance 484:95965c546ae80dd61779, statement 30943. -/
def sourceState_186 : IndexState := ⟨2, 3⟩
theorem guard_186 : indexGuard sourceState_186 := fixed_guard 2 0
theorem certificate_186 {α : Type} (normal first second : Result α) :
    ¬ diagnostic (indexGuard sourceState_186) ∧
      branch (indexGuard sourceState_186) normal first =
        branch (indexGuard sourceState_186) normal second :=
  fixed_certificate 2 0 normal first second
#print axioms guard_186
#print axioms certificate_186
/-- Actual source instance 522:95965c546ae80dd61779, statement 31223. -/
def sourceState_187 : IndexState := ⟨0, 3⟩
theorem guard_187 : indexGuard sourceState_187 := fixed_guard 0 2
theorem certificate_187 {α : Type} (normal first second : Result α) :
    ¬ diagnostic (indexGuard sourceState_187) ∧
      branch (indexGuard sourceState_187) normal first =
        branch (indexGuard sourceState_187) normal second :=
  fixed_certificate 0 2 normal first second
#print axioms guard_187
#print axioms certificate_187
/-- Actual source instance 522:95965c546ae80dd61779, statement 31228. -/
def sourceState_188 : IndexState := ⟨1, 3⟩
theorem guard_188 : indexGuard sourceState_188 := fixed_guard 1 1
theorem certificate_188 {α : Type} (normal first second : Result α) :
    ¬ diagnostic (indexGuard sourceState_188) ∧
      branch (indexGuard sourceState_188) normal first =
        branch (indexGuard sourceState_188) normal second :=
  fixed_certificate 1 1 normal first second
#print axioms guard_188
#print axioms certificate_188
/-- Actual source instance 522:95965c546ae80dd61779, statement 31233. -/
def sourceState_189 : IndexState := ⟨2, 3⟩
theorem guard_189 : indexGuard sourceState_189 := fixed_guard 2 0
theorem certificate_189 {α : Type} (normal first second : Result α) :
    ¬ diagnostic (indexGuard sourceState_189) ∧
      branch (indexGuard sourceState_189) normal first =
        branch (indexGuard sourceState_189) normal second :=
  fixed_certificate 2 0 normal first second
#print axioms guard_189
#print axioms certificate_189
/-- Actual source instance 536:95965c546ae80dd61779, statement 31278. -/
def sourceState_190 : IndexState := ⟨0, 4⟩
theorem guard_190 : indexGuard sourceState_190 := fixed_guard 0 3
theorem certificate_190 {α : Type} (normal first second : Result α) :
    ¬ diagnostic (indexGuard sourceState_190) ∧
      branch (indexGuard sourceState_190) normal first =
        branch (indexGuard sourceState_190) normal second :=
  fixed_certificate 0 3 normal first second
#print axioms guard_190
#print axioms certificate_190
/-- Actual source instance 536:95965c546ae80dd61779, statement 31288. -/
def sourceState_191 : IndexState := ⟨1, 4⟩
theorem guard_191 : indexGuard sourceState_191 := fixed_guard 1 2
theorem certificate_191 {α : Type} (normal first second : Result α) :
    ¬ diagnostic (indexGuard sourceState_191) ∧
      branch (indexGuard sourceState_191) normal first =
        branch (indexGuard sourceState_191) normal second :=
  fixed_certificate 1 2 normal first second
#print axioms guard_191
#print axioms certificate_191
end PV_B3P_FixedIndices572227_05
