import AspisV8R19.R799LiteralSourceMatrix
import Mathlib.Tactic.FinCases

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 800000
namespace AspisV8R19.R801LiteralActiveEntries
open AspisV8R17
open AspisV8R19.R738JointObservationModel
open AspisV8R19.R743JointSparseEntryBinding
open AspisV8R19.R798LiteralObservationView
open AspisV8R19.R799LiteralSourceMatrix
noncomputable section

def activeCodes : List Nat := [114, 116, 118, 120, 122, 124, 126, 128, 130, 132, 134, 136, 138, 140, 142, 144, 146, 148, 150, 152, 154, 156, 158, 160, 162, 164, 166, 168, 170, 172, 174, 176, 178, 180, 184, 190, 194, 196, 198, 200, 202, 204, 206, 208, 210, 212, 214, 216, 218, 220, 222, 224, 226, 228, 230, 232, 234, 236, 238, 240, 243, 245, 247, 249, 251, 253, 257, 259, 261, 263, 265, 267, 269, 271, 273, 275, 277, 279, 281, 283, 285, 287, 289, 291, 293, 295, 297, 299, 301, 303, 305, 307, 311, 313, 315, 317, 319, 321, 323, 325, 327, 329, 331, 333, 335, 337, 339, 341, 343, 345, 347, 349, 351, 353, 355, 357, 359, 361, 365, 367, 370, 372, 374, 376, 378, 380, 382, 499, 501, 503, 505, 507, 509, 511, 626, 628, 630, 632, 634, 636, 638, 639, 755, 757, 759, 761, 763, 765, 766, 882, 884, 886, 888, 890, 892, 894, 900, 902, 904, 906, 908, 910, 912, 914, 916, 918, 920, 922, 924, 926, 928, 930, 932, 934, 936, 938, 940, 942, 944, 948, 952, 954, 958, 960, 962, 964, 966, 968, 970, 972, 974, 976, 978, 980, 982, 984, 986, 988, 990, 992, 994, 996, 998, 1000, 1002, 1004, 1006, 1008, 1011, 1013, 1015, 1017, 1019, 1022]
theorem activeCodes_length : activeCodes.length = 214 := rfl

def activeCodeView (i : Fin 214) : Nat :=
  activeCodes.get (Fin.cast activeCodes_length.symm i)

def activePosition (i : Fin 214) : Fin 222 := Fin.castLE (by decide) i

theorem activeCodeView_bounds (i : Fin 214) :
    96 ≤ activeCodeView i ∧ activeCodeView i < 1024 := by
  revert i
  decide

variable {F : Type*} [CommRing F] [Nontrivial F]
theorem literalSourceMatrix_active_entry (half quarter alpha u v kappa tau : F)
    (z : Fin 10 → F) (i : Fin 214) (j : Fin 222) :
    literalSourceMatrix half quarter alpha u v kappa tau z (activePosition i) j =
      sourceChord half (direction alpha (columnView j).1 (columnView j).2)
        (1+u*v) (u*v-1) (-(u+v)) (activeCodeView i) := by
  rw [literalSourceMatrix_entry]
  fin_cases i
  case «0» =>
    change sourceChord half (rawFlatten (indexedDirection alpha (columnView j).1 (columnView j).2))
      (1+u*v) (u*v-1) (-(u+v)) 114 =
      sourceChord half (direction alpha (columnView j).1 (columnView j).2)
        (1+u*v) (u*v-1) (-(u+v)) 114
    rw [rawFlatten_indexedDirection]
  case «1» =>
    change sourceChord half (rawFlatten (indexedDirection alpha (columnView j).1 (columnView j).2))
      (1+u*v) (u*v-1) (-(u+v)) 116 =
      sourceChord half (direction alpha (columnView j).1 (columnView j).2)
        (1+u*v) (u*v-1) (-(u+v)) 116
    rw [rawFlatten_indexedDirection]
  case «2» =>
    change sourceChord half (rawFlatten (indexedDirection alpha (columnView j).1 (columnView j).2))
      (1+u*v) (u*v-1) (-(u+v)) 118 =
      sourceChord half (direction alpha (columnView j).1 (columnView j).2)
        (1+u*v) (u*v-1) (-(u+v)) 118
    rw [rawFlatten_indexedDirection]
  case «3» =>
    change sourceChord half (rawFlatten (indexedDirection alpha (columnView j).1 (columnView j).2))
      (1+u*v) (u*v-1) (-(u+v)) 120 =
      sourceChord half (direction alpha (columnView j).1 (columnView j).2)
        (1+u*v) (u*v-1) (-(u+v)) 120
    rw [rawFlatten_indexedDirection]
  case «4» =>
    change sourceChord half (rawFlatten (indexedDirection alpha (columnView j).1 (columnView j).2))
      (1+u*v) (u*v-1) (-(u+v)) 122 =
      sourceChord half (direction alpha (columnView j).1 (columnView j).2)
        (1+u*v) (u*v-1) (-(u+v)) 122
    rw [rawFlatten_indexedDirection]
  case «5» =>
    change sourceChord half (rawFlatten (indexedDirection alpha (columnView j).1 (columnView j).2))
      (1+u*v) (u*v-1) (-(u+v)) 124 =
      sourceChord half (direction alpha (columnView j).1 (columnView j).2)
        (1+u*v) (u*v-1) (-(u+v)) 124
    rw [rawFlatten_indexedDirection]
  case «6» =>
    change sourceChord half (rawFlatten (indexedDirection alpha (columnView j).1 (columnView j).2))
      (1+u*v) (u*v-1) (-(u+v)) 126 =
      sourceChord half (direction alpha (columnView j).1 (columnView j).2)
        (1+u*v) (u*v-1) (-(u+v)) 126
    rw [rawFlatten_indexedDirection]
  case «7» =>
    change sourceChord half (rawFlatten (indexedDirection alpha (columnView j).1 (columnView j).2))
      (1+u*v) (u*v-1) (-(u+v)) 128 =
      sourceChord half (direction alpha (columnView j).1 (columnView j).2)
        (1+u*v) (u*v-1) (-(u+v)) 128
    rw [rawFlatten_indexedDirection]
  case «8» =>
    change sourceChord half (rawFlatten (indexedDirection alpha (columnView j).1 (columnView j).2))
      (1+u*v) (u*v-1) (-(u+v)) 130 =
      sourceChord half (direction alpha (columnView j).1 (columnView j).2)
        (1+u*v) (u*v-1) (-(u+v)) 130
    rw [rawFlatten_indexedDirection]
  case «9» =>
    change sourceChord half (rawFlatten (indexedDirection alpha (columnView j).1 (columnView j).2))
      (1+u*v) (u*v-1) (-(u+v)) 132 =
      sourceChord half (direction alpha (columnView j).1 (columnView j).2)
        (1+u*v) (u*v-1) (-(u+v)) 132
    rw [rawFlatten_indexedDirection]
  case «10» =>
    change sourceChord half (rawFlatten (indexedDirection alpha (columnView j).1 (columnView j).2))
      (1+u*v) (u*v-1) (-(u+v)) 134 =
      sourceChord half (direction alpha (columnView j).1 (columnView j).2)
        (1+u*v) (u*v-1) (-(u+v)) 134
    rw [rawFlatten_indexedDirection]
  case «11» =>
    change sourceChord half (rawFlatten (indexedDirection alpha (columnView j).1 (columnView j).2))
      (1+u*v) (u*v-1) (-(u+v)) 136 =
      sourceChord half (direction alpha (columnView j).1 (columnView j).2)
        (1+u*v) (u*v-1) (-(u+v)) 136
    rw [rawFlatten_indexedDirection]
  case «12» =>
    change sourceChord half (rawFlatten (indexedDirection alpha (columnView j).1 (columnView j).2))
      (1+u*v) (u*v-1) (-(u+v)) 138 =
      sourceChord half (direction alpha (columnView j).1 (columnView j).2)
        (1+u*v) (u*v-1) (-(u+v)) 138
    rw [rawFlatten_indexedDirection]
  case «13» =>
    change sourceChord half (rawFlatten (indexedDirection alpha (columnView j).1 (columnView j).2))
      (1+u*v) (u*v-1) (-(u+v)) 140 =
      sourceChord half (direction alpha (columnView j).1 (columnView j).2)
        (1+u*v) (u*v-1) (-(u+v)) 140
    rw [rawFlatten_indexedDirection]
  case «14» =>
    change sourceChord half (rawFlatten (indexedDirection alpha (columnView j).1 (columnView j).2))
      (1+u*v) (u*v-1) (-(u+v)) 142 =
      sourceChord half (direction alpha (columnView j).1 (columnView j).2)
        (1+u*v) (u*v-1) (-(u+v)) 142
    rw [rawFlatten_indexedDirection]
  case «15» =>
    change sourceChord half (rawFlatten (indexedDirection alpha (columnView j).1 (columnView j).2))
      (1+u*v) (u*v-1) (-(u+v)) 144 =
      sourceChord half (direction alpha (columnView j).1 (columnView j).2)
        (1+u*v) (u*v-1) (-(u+v)) 144
    rw [rawFlatten_indexedDirection]
  case «16» =>
    change sourceChord half (rawFlatten (indexedDirection alpha (columnView j).1 (columnView j).2))
      (1+u*v) (u*v-1) (-(u+v)) 146 =
      sourceChord half (direction alpha (columnView j).1 (columnView j).2)
        (1+u*v) (u*v-1) (-(u+v)) 146
    rw [rawFlatten_indexedDirection]
  case «17» =>
    change sourceChord half (rawFlatten (indexedDirection alpha (columnView j).1 (columnView j).2))
      (1+u*v) (u*v-1) (-(u+v)) 148 =
      sourceChord half (direction alpha (columnView j).1 (columnView j).2)
        (1+u*v) (u*v-1) (-(u+v)) 148
    rw [rawFlatten_indexedDirection]
  case «18» =>
    change sourceChord half (rawFlatten (indexedDirection alpha (columnView j).1 (columnView j).2))
      (1+u*v) (u*v-1) (-(u+v)) 150 =
      sourceChord half (direction alpha (columnView j).1 (columnView j).2)
        (1+u*v) (u*v-1) (-(u+v)) 150
    rw [rawFlatten_indexedDirection]
  case «19» =>
    change sourceChord half (rawFlatten (indexedDirection alpha (columnView j).1 (columnView j).2))
      (1+u*v) (u*v-1) (-(u+v)) 152 =
      sourceChord half (direction alpha (columnView j).1 (columnView j).2)
        (1+u*v) (u*v-1) (-(u+v)) 152
    rw [rawFlatten_indexedDirection]
  case «20» =>
    change sourceChord half (rawFlatten (indexedDirection alpha (columnView j).1 (columnView j).2))
      (1+u*v) (u*v-1) (-(u+v)) 154 =
      sourceChord half (direction alpha (columnView j).1 (columnView j).2)
        (1+u*v) (u*v-1) (-(u+v)) 154
    rw [rawFlatten_indexedDirection]
  case «21» =>
    change sourceChord half (rawFlatten (indexedDirection alpha (columnView j).1 (columnView j).2))
      (1+u*v) (u*v-1) (-(u+v)) 156 =
      sourceChord half (direction alpha (columnView j).1 (columnView j).2)
        (1+u*v) (u*v-1) (-(u+v)) 156
    rw [rawFlatten_indexedDirection]
  case «22» =>
    change sourceChord half (rawFlatten (indexedDirection alpha (columnView j).1 (columnView j).2))
      (1+u*v) (u*v-1) (-(u+v)) 158 =
      sourceChord half (direction alpha (columnView j).1 (columnView j).2)
        (1+u*v) (u*v-1) (-(u+v)) 158
    rw [rawFlatten_indexedDirection]
  case «23» =>
    change sourceChord half (rawFlatten (indexedDirection alpha (columnView j).1 (columnView j).2))
      (1+u*v) (u*v-1) (-(u+v)) 160 =
      sourceChord half (direction alpha (columnView j).1 (columnView j).2)
        (1+u*v) (u*v-1) (-(u+v)) 160
    rw [rawFlatten_indexedDirection]
  case «24» =>
    change sourceChord half (rawFlatten (indexedDirection alpha (columnView j).1 (columnView j).2))
      (1+u*v) (u*v-1) (-(u+v)) 162 =
      sourceChord half (direction alpha (columnView j).1 (columnView j).2)
        (1+u*v) (u*v-1) (-(u+v)) 162
    rw [rawFlatten_indexedDirection]
  case «25» =>
    change sourceChord half (rawFlatten (indexedDirection alpha (columnView j).1 (columnView j).2))
      (1+u*v) (u*v-1) (-(u+v)) 164 =
      sourceChord half (direction alpha (columnView j).1 (columnView j).2)
        (1+u*v) (u*v-1) (-(u+v)) 164
    rw [rawFlatten_indexedDirection]
  case «26» =>
    change sourceChord half (rawFlatten (indexedDirection alpha (columnView j).1 (columnView j).2))
      (1+u*v) (u*v-1) (-(u+v)) 166 =
      sourceChord half (direction alpha (columnView j).1 (columnView j).2)
        (1+u*v) (u*v-1) (-(u+v)) 166
    rw [rawFlatten_indexedDirection]
  case «27» =>
    change sourceChord half (rawFlatten (indexedDirection alpha (columnView j).1 (columnView j).2))
      (1+u*v) (u*v-1) (-(u+v)) 168 =
      sourceChord half (direction alpha (columnView j).1 (columnView j).2)
        (1+u*v) (u*v-1) (-(u+v)) 168
    rw [rawFlatten_indexedDirection]
  case «28» =>
    change sourceChord half (rawFlatten (indexedDirection alpha (columnView j).1 (columnView j).2))
      (1+u*v) (u*v-1) (-(u+v)) 170 =
      sourceChord half (direction alpha (columnView j).1 (columnView j).2)
        (1+u*v) (u*v-1) (-(u+v)) 170
    rw [rawFlatten_indexedDirection]
  case «29» =>
    change sourceChord half (rawFlatten (indexedDirection alpha (columnView j).1 (columnView j).2))
      (1+u*v) (u*v-1) (-(u+v)) 172 =
      sourceChord half (direction alpha (columnView j).1 (columnView j).2)
        (1+u*v) (u*v-1) (-(u+v)) 172
    rw [rawFlatten_indexedDirection]
  case «30» =>
    change sourceChord half (rawFlatten (indexedDirection alpha (columnView j).1 (columnView j).2))
      (1+u*v) (u*v-1) (-(u+v)) 174 =
      sourceChord half (direction alpha (columnView j).1 (columnView j).2)
        (1+u*v) (u*v-1) (-(u+v)) 174
    rw [rawFlatten_indexedDirection]
  case «31» =>
    change sourceChord half (rawFlatten (indexedDirection alpha (columnView j).1 (columnView j).2))
      (1+u*v) (u*v-1) (-(u+v)) 176 =
      sourceChord half (direction alpha (columnView j).1 (columnView j).2)
        (1+u*v) (u*v-1) (-(u+v)) 176
    rw [rawFlatten_indexedDirection]
  case «32» =>
    change sourceChord half (rawFlatten (indexedDirection alpha (columnView j).1 (columnView j).2))
      (1+u*v) (u*v-1) (-(u+v)) 178 =
      sourceChord half (direction alpha (columnView j).1 (columnView j).2)
        (1+u*v) (u*v-1) (-(u+v)) 178
    rw [rawFlatten_indexedDirection]
  case «33» =>
    change sourceChord half (rawFlatten (indexedDirection alpha (columnView j).1 (columnView j).2))
      (1+u*v) (u*v-1) (-(u+v)) 180 =
      sourceChord half (direction alpha (columnView j).1 (columnView j).2)
        (1+u*v) (u*v-1) (-(u+v)) 180
    rw [rawFlatten_indexedDirection]
  case «34» =>
    change sourceChord half (rawFlatten (indexedDirection alpha (columnView j).1 (columnView j).2))
      (1+u*v) (u*v-1) (-(u+v)) 184 =
      sourceChord half (direction alpha (columnView j).1 (columnView j).2)
        (1+u*v) (u*v-1) (-(u+v)) 184
    rw [rawFlatten_indexedDirection]
  case «35» =>
    change sourceChord half (rawFlatten (indexedDirection alpha (columnView j).1 (columnView j).2))
      (1+u*v) (u*v-1) (-(u+v)) 190 =
      sourceChord half (direction alpha (columnView j).1 (columnView j).2)
        (1+u*v) (u*v-1) (-(u+v)) 190
    rw [rawFlatten_indexedDirection]
  case «36» =>
    change sourceChord half (rawFlatten (indexedDirection alpha (columnView j).1 (columnView j).2))
      (1+u*v) (u*v-1) (-(u+v)) 194 =
      sourceChord half (direction alpha (columnView j).1 (columnView j).2)
        (1+u*v) (u*v-1) (-(u+v)) 194
    rw [rawFlatten_indexedDirection]
  case «37» =>
    change sourceChord half (rawFlatten (indexedDirection alpha (columnView j).1 (columnView j).2))
      (1+u*v) (u*v-1) (-(u+v)) 196 =
      sourceChord half (direction alpha (columnView j).1 (columnView j).2)
        (1+u*v) (u*v-1) (-(u+v)) 196
    rw [rawFlatten_indexedDirection]
  case «38» =>
    change sourceChord half (rawFlatten (indexedDirection alpha (columnView j).1 (columnView j).2))
      (1+u*v) (u*v-1) (-(u+v)) 198 =
      sourceChord half (direction alpha (columnView j).1 (columnView j).2)
        (1+u*v) (u*v-1) (-(u+v)) 198
    rw [rawFlatten_indexedDirection]
  case «39» =>
    change sourceChord half (rawFlatten (indexedDirection alpha (columnView j).1 (columnView j).2))
      (1+u*v) (u*v-1) (-(u+v)) 200 =
      sourceChord half (direction alpha (columnView j).1 (columnView j).2)
        (1+u*v) (u*v-1) (-(u+v)) 200
    rw [rawFlatten_indexedDirection]
  case «40» =>
    change sourceChord half (rawFlatten (indexedDirection alpha (columnView j).1 (columnView j).2))
      (1+u*v) (u*v-1) (-(u+v)) 202 =
      sourceChord half (direction alpha (columnView j).1 (columnView j).2)
        (1+u*v) (u*v-1) (-(u+v)) 202
    rw [rawFlatten_indexedDirection]
  case «41» =>
    change sourceChord half (rawFlatten (indexedDirection alpha (columnView j).1 (columnView j).2))
      (1+u*v) (u*v-1) (-(u+v)) 204 =
      sourceChord half (direction alpha (columnView j).1 (columnView j).2)
        (1+u*v) (u*v-1) (-(u+v)) 204
    rw [rawFlatten_indexedDirection]
  case «42» =>
    change sourceChord half (rawFlatten (indexedDirection alpha (columnView j).1 (columnView j).2))
      (1+u*v) (u*v-1) (-(u+v)) 206 =
      sourceChord half (direction alpha (columnView j).1 (columnView j).2)
        (1+u*v) (u*v-1) (-(u+v)) 206
    rw [rawFlatten_indexedDirection]
  case «43» =>
    change sourceChord half (rawFlatten (indexedDirection alpha (columnView j).1 (columnView j).2))
      (1+u*v) (u*v-1) (-(u+v)) 208 =
      sourceChord half (direction alpha (columnView j).1 (columnView j).2)
        (1+u*v) (u*v-1) (-(u+v)) 208
    rw [rawFlatten_indexedDirection]
  case «44» =>
    change sourceChord half (rawFlatten (indexedDirection alpha (columnView j).1 (columnView j).2))
      (1+u*v) (u*v-1) (-(u+v)) 210 =
      sourceChord half (direction alpha (columnView j).1 (columnView j).2)
        (1+u*v) (u*v-1) (-(u+v)) 210
    rw [rawFlatten_indexedDirection]
  case «45» =>
    change sourceChord half (rawFlatten (indexedDirection alpha (columnView j).1 (columnView j).2))
      (1+u*v) (u*v-1) (-(u+v)) 212 =
      sourceChord half (direction alpha (columnView j).1 (columnView j).2)
        (1+u*v) (u*v-1) (-(u+v)) 212
    rw [rawFlatten_indexedDirection]
  case «46» =>
    change sourceChord half (rawFlatten (indexedDirection alpha (columnView j).1 (columnView j).2))
      (1+u*v) (u*v-1) (-(u+v)) 214 =
      sourceChord half (direction alpha (columnView j).1 (columnView j).2)
        (1+u*v) (u*v-1) (-(u+v)) 214
    rw [rawFlatten_indexedDirection]
  case «47» =>
    change sourceChord half (rawFlatten (indexedDirection alpha (columnView j).1 (columnView j).2))
      (1+u*v) (u*v-1) (-(u+v)) 216 =
      sourceChord half (direction alpha (columnView j).1 (columnView j).2)
        (1+u*v) (u*v-1) (-(u+v)) 216
    rw [rawFlatten_indexedDirection]
  case «48» =>
    change sourceChord half (rawFlatten (indexedDirection alpha (columnView j).1 (columnView j).2))
      (1+u*v) (u*v-1) (-(u+v)) 218 =
      sourceChord half (direction alpha (columnView j).1 (columnView j).2)
        (1+u*v) (u*v-1) (-(u+v)) 218
    rw [rawFlatten_indexedDirection]
  case «49» =>
    change sourceChord half (rawFlatten (indexedDirection alpha (columnView j).1 (columnView j).2))
      (1+u*v) (u*v-1) (-(u+v)) 220 =
      sourceChord half (direction alpha (columnView j).1 (columnView j).2)
        (1+u*v) (u*v-1) (-(u+v)) 220
    rw [rawFlatten_indexedDirection]
  case «50» =>
    change sourceChord half (rawFlatten (indexedDirection alpha (columnView j).1 (columnView j).2))
      (1+u*v) (u*v-1) (-(u+v)) 222 =
      sourceChord half (direction alpha (columnView j).1 (columnView j).2)
        (1+u*v) (u*v-1) (-(u+v)) 222
    rw [rawFlatten_indexedDirection]
  case «51» =>
    change sourceChord half (rawFlatten (indexedDirection alpha (columnView j).1 (columnView j).2))
      (1+u*v) (u*v-1) (-(u+v)) 224 =
      sourceChord half (direction alpha (columnView j).1 (columnView j).2)
        (1+u*v) (u*v-1) (-(u+v)) 224
    rw [rawFlatten_indexedDirection]
  case «52» =>
    change sourceChord half (rawFlatten (indexedDirection alpha (columnView j).1 (columnView j).2))
      (1+u*v) (u*v-1) (-(u+v)) 226 =
      sourceChord half (direction alpha (columnView j).1 (columnView j).2)
        (1+u*v) (u*v-1) (-(u+v)) 226
    rw [rawFlatten_indexedDirection]
  case «53» =>
    change sourceChord half (rawFlatten (indexedDirection alpha (columnView j).1 (columnView j).2))
      (1+u*v) (u*v-1) (-(u+v)) 228 =
      sourceChord half (direction alpha (columnView j).1 (columnView j).2)
        (1+u*v) (u*v-1) (-(u+v)) 228
    rw [rawFlatten_indexedDirection]
  case «54» =>
    change sourceChord half (rawFlatten (indexedDirection alpha (columnView j).1 (columnView j).2))
      (1+u*v) (u*v-1) (-(u+v)) 230 =
      sourceChord half (direction alpha (columnView j).1 (columnView j).2)
        (1+u*v) (u*v-1) (-(u+v)) 230
    rw [rawFlatten_indexedDirection]
  case «55» =>
    change sourceChord half (rawFlatten (indexedDirection alpha (columnView j).1 (columnView j).2))
      (1+u*v) (u*v-1) (-(u+v)) 232 =
      sourceChord half (direction alpha (columnView j).1 (columnView j).2)
        (1+u*v) (u*v-1) (-(u+v)) 232
    rw [rawFlatten_indexedDirection]
  case «56» =>
    change sourceChord half (rawFlatten (indexedDirection alpha (columnView j).1 (columnView j).2))
      (1+u*v) (u*v-1) (-(u+v)) 234 =
      sourceChord half (direction alpha (columnView j).1 (columnView j).2)
        (1+u*v) (u*v-1) (-(u+v)) 234
    rw [rawFlatten_indexedDirection]
  case «57» =>
    change sourceChord half (rawFlatten (indexedDirection alpha (columnView j).1 (columnView j).2))
      (1+u*v) (u*v-1) (-(u+v)) 236 =
      sourceChord half (direction alpha (columnView j).1 (columnView j).2)
        (1+u*v) (u*v-1) (-(u+v)) 236
    rw [rawFlatten_indexedDirection]
  case «58» =>
    change sourceChord half (rawFlatten (indexedDirection alpha (columnView j).1 (columnView j).2))
      (1+u*v) (u*v-1) (-(u+v)) 238 =
      sourceChord half (direction alpha (columnView j).1 (columnView j).2)
        (1+u*v) (u*v-1) (-(u+v)) 238
    rw [rawFlatten_indexedDirection]
  case «59» =>
    change sourceChord half (rawFlatten (indexedDirection alpha (columnView j).1 (columnView j).2))
      (1+u*v) (u*v-1) (-(u+v)) 240 =
      sourceChord half (direction alpha (columnView j).1 (columnView j).2)
        (1+u*v) (u*v-1) (-(u+v)) 240
    rw [rawFlatten_indexedDirection]
  case «60» =>
    change sourceChord half (rawFlatten (indexedDirection alpha (columnView j).1 (columnView j).2))
      (1+u*v) (u*v-1) (-(u+v)) 243 =
      sourceChord half (direction alpha (columnView j).1 (columnView j).2)
        (1+u*v) (u*v-1) (-(u+v)) 243
    rw [rawFlatten_indexedDirection]
  case «61» =>
    change sourceChord half (rawFlatten (indexedDirection alpha (columnView j).1 (columnView j).2))
      (1+u*v) (u*v-1) (-(u+v)) 245 =
      sourceChord half (direction alpha (columnView j).1 (columnView j).2)
        (1+u*v) (u*v-1) (-(u+v)) 245
    rw [rawFlatten_indexedDirection]
  case «62» =>
    change sourceChord half (rawFlatten (indexedDirection alpha (columnView j).1 (columnView j).2))
      (1+u*v) (u*v-1) (-(u+v)) 247 =
      sourceChord half (direction alpha (columnView j).1 (columnView j).2)
        (1+u*v) (u*v-1) (-(u+v)) 247
    rw [rawFlatten_indexedDirection]
  case «63» =>
    change sourceChord half (rawFlatten (indexedDirection alpha (columnView j).1 (columnView j).2))
      (1+u*v) (u*v-1) (-(u+v)) 249 =
      sourceChord half (direction alpha (columnView j).1 (columnView j).2)
        (1+u*v) (u*v-1) (-(u+v)) 249
    rw [rawFlatten_indexedDirection]
  case «64» =>
    change sourceChord half (rawFlatten (indexedDirection alpha (columnView j).1 (columnView j).2))
      (1+u*v) (u*v-1) (-(u+v)) 251 =
      sourceChord half (direction alpha (columnView j).1 (columnView j).2)
        (1+u*v) (u*v-1) (-(u+v)) 251
    rw [rawFlatten_indexedDirection]
  case «65» =>
    change sourceChord half (rawFlatten (indexedDirection alpha (columnView j).1 (columnView j).2))
      (1+u*v) (u*v-1) (-(u+v)) 253 =
      sourceChord half (direction alpha (columnView j).1 (columnView j).2)
        (1+u*v) (u*v-1) (-(u+v)) 253
    rw [rawFlatten_indexedDirection]
  case «66» =>
    change sourceChord half (rawFlatten (indexedDirection alpha (columnView j).1 (columnView j).2))
      (1+u*v) (u*v-1) (-(u+v)) 257 =
      sourceChord half (direction alpha (columnView j).1 (columnView j).2)
        (1+u*v) (u*v-1) (-(u+v)) 257
    rw [rawFlatten_indexedDirection]
  case «67» =>
    change sourceChord half (rawFlatten (indexedDirection alpha (columnView j).1 (columnView j).2))
      (1+u*v) (u*v-1) (-(u+v)) 259 =
      sourceChord half (direction alpha (columnView j).1 (columnView j).2)
        (1+u*v) (u*v-1) (-(u+v)) 259
    rw [rawFlatten_indexedDirection]
  case «68» =>
    change sourceChord half (rawFlatten (indexedDirection alpha (columnView j).1 (columnView j).2))
      (1+u*v) (u*v-1) (-(u+v)) 261 =
      sourceChord half (direction alpha (columnView j).1 (columnView j).2)
        (1+u*v) (u*v-1) (-(u+v)) 261
    rw [rawFlatten_indexedDirection]
  case «69» =>
    change sourceChord half (rawFlatten (indexedDirection alpha (columnView j).1 (columnView j).2))
      (1+u*v) (u*v-1) (-(u+v)) 263 =
      sourceChord half (direction alpha (columnView j).1 (columnView j).2)
        (1+u*v) (u*v-1) (-(u+v)) 263
    rw [rawFlatten_indexedDirection]
  case «70» =>
    change sourceChord half (rawFlatten (indexedDirection alpha (columnView j).1 (columnView j).2))
      (1+u*v) (u*v-1) (-(u+v)) 265 =
      sourceChord half (direction alpha (columnView j).1 (columnView j).2)
        (1+u*v) (u*v-1) (-(u+v)) 265
    rw [rawFlatten_indexedDirection]
  case «71» =>
    change sourceChord half (rawFlatten (indexedDirection alpha (columnView j).1 (columnView j).2))
      (1+u*v) (u*v-1) (-(u+v)) 267 =
      sourceChord half (direction alpha (columnView j).1 (columnView j).2)
        (1+u*v) (u*v-1) (-(u+v)) 267
    rw [rawFlatten_indexedDirection]
  case «72» =>
    change sourceChord half (rawFlatten (indexedDirection alpha (columnView j).1 (columnView j).2))
      (1+u*v) (u*v-1) (-(u+v)) 269 =
      sourceChord half (direction alpha (columnView j).1 (columnView j).2)
        (1+u*v) (u*v-1) (-(u+v)) 269
    rw [rawFlatten_indexedDirection]
  case «73» =>
    change sourceChord half (rawFlatten (indexedDirection alpha (columnView j).1 (columnView j).2))
      (1+u*v) (u*v-1) (-(u+v)) 271 =
      sourceChord half (direction alpha (columnView j).1 (columnView j).2)
        (1+u*v) (u*v-1) (-(u+v)) 271
    rw [rawFlatten_indexedDirection]
  case «74» =>
    change sourceChord half (rawFlatten (indexedDirection alpha (columnView j).1 (columnView j).2))
      (1+u*v) (u*v-1) (-(u+v)) 273 =
      sourceChord half (direction alpha (columnView j).1 (columnView j).2)
        (1+u*v) (u*v-1) (-(u+v)) 273
    rw [rawFlatten_indexedDirection]
  case «75» =>
    change sourceChord half (rawFlatten (indexedDirection alpha (columnView j).1 (columnView j).2))
      (1+u*v) (u*v-1) (-(u+v)) 275 =
      sourceChord half (direction alpha (columnView j).1 (columnView j).2)
        (1+u*v) (u*v-1) (-(u+v)) 275
    rw [rawFlatten_indexedDirection]
  case «76» =>
    change sourceChord half (rawFlatten (indexedDirection alpha (columnView j).1 (columnView j).2))
      (1+u*v) (u*v-1) (-(u+v)) 277 =
      sourceChord half (direction alpha (columnView j).1 (columnView j).2)
        (1+u*v) (u*v-1) (-(u+v)) 277
    rw [rawFlatten_indexedDirection]
  case «77» =>
    change sourceChord half (rawFlatten (indexedDirection alpha (columnView j).1 (columnView j).2))
      (1+u*v) (u*v-1) (-(u+v)) 279 =
      sourceChord half (direction alpha (columnView j).1 (columnView j).2)
        (1+u*v) (u*v-1) (-(u+v)) 279
    rw [rawFlatten_indexedDirection]
  case «78» =>
    change sourceChord half (rawFlatten (indexedDirection alpha (columnView j).1 (columnView j).2))
      (1+u*v) (u*v-1) (-(u+v)) 281 =
      sourceChord half (direction alpha (columnView j).1 (columnView j).2)
        (1+u*v) (u*v-1) (-(u+v)) 281
    rw [rawFlatten_indexedDirection]
  case «79» =>
    change sourceChord half (rawFlatten (indexedDirection alpha (columnView j).1 (columnView j).2))
      (1+u*v) (u*v-1) (-(u+v)) 283 =
      sourceChord half (direction alpha (columnView j).1 (columnView j).2)
        (1+u*v) (u*v-1) (-(u+v)) 283
    rw [rawFlatten_indexedDirection]
  case «80» =>
    change sourceChord half (rawFlatten (indexedDirection alpha (columnView j).1 (columnView j).2))
      (1+u*v) (u*v-1) (-(u+v)) 285 =
      sourceChord half (direction alpha (columnView j).1 (columnView j).2)
        (1+u*v) (u*v-1) (-(u+v)) 285
    rw [rawFlatten_indexedDirection]
  case «81» =>
    change sourceChord half (rawFlatten (indexedDirection alpha (columnView j).1 (columnView j).2))
      (1+u*v) (u*v-1) (-(u+v)) 287 =
      sourceChord half (direction alpha (columnView j).1 (columnView j).2)
        (1+u*v) (u*v-1) (-(u+v)) 287
    rw [rawFlatten_indexedDirection]
  case «82» =>
    change sourceChord half (rawFlatten (indexedDirection alpha (columnView j).1 (columnView j).2))
      (1+u*v) (u*v-1) (-(u+v)) 289 =
      sourceChord half (direction alpha (columnView j).1 (columnView j).2)
        (1+u*v) (u*v-1) (-(u+v)) 289
    rw [rawFlatten_indexedDirection]
  case «83» =>
    change sourceChord half (rawFlatten (indexedDirection alpha (columnView j).1 (columnView j).2))
      (1+u*v) (u*v-1) (-(u+v)) 291 =
      sourceChord half (direction alpha (columnView j).1 (columnView j).2)
        (1+u*v) (u*v-1) (-(u+v)) 291
    rw [rawFlatten_indexedDirection]
  case «84» =>
    change sourceChord half (rawFlatten (indexedDirection alpha (columnView j).1 (columnView j).2))
      (1+u*v) (u*v-1) (-(u+v)) 293 =
      sourceChord half (direction alpha (columnView j).1 (columnView j).2)
        (1+u*v) (u*v-1) (-(u+v)) 293
    rw [rawFlatten_indexedDirection]
  case «85» =>
    change sourceChord half (rawFlatten (indexedDirection alpha (columnView j).1 (columnView j).2))
      (1+u*v) (u*v-1) (-(u+v)) 295 =
      sourceChord half (direction alpha (columnView j).1 (columnView j).2)
        (1+u*v) (u*v-1) (-(u+v)) 295
    rw [rawFlatten_indexedDirection]
  case «86» =>
    change sourceChord half (rawFlatten (indexedDirection alpha (columnView j).1 (columnView j).2))
      (1+u*v) (u*v-1) (-(u+v)) 297 =
      sourceChord half (direction alpha (columnView j).1 (columnView j).2)
        (1+u*v) (u*v-1) (-(u+v)) 297
    rw [rawFlatten_indexedDirection]
  case «87» =>
    change sourceChord half (rawFlatten (indexedDirection alpha (columnView j).1 (columnView j).2))
      (1+u*v) (u*v-1) (-(u+v)) 299 =
      sourceChord half (direction alpha (columnView j).1 (columnView j).2)
        (1+u*v) (u*v-1) (-(u+v)) 299
    rw [rawFlatten_indexedDirection]
  case «88» =>
    change sourceChord half (rawFlatten (indexedDirection alpha (columnView j).1 (columnView j).2))
      (1+u*v) (u*v-1) (-(u+v)) 301 =
      sourceChord half (direction alpha (columnView j).1 (columnView j).2)
        (1+u*v) (u*v-1) (-(u+v)) 301
    rw [rawFlatten_indexedDirection]
  case «89» =>
    change sourceChord half (rawFlatten (indexedDirection alpha (columnView j).1 (columnView j).2))
      (1+u*v) (u*v-1) (-(u+v)) 303 =
      sourceChord half (direction alpha (columnView j).1 (columnView j).2)
        (1+u*v) (u*v-1) (-(u+v)) 303
    rw [rawFlatten_indexedDirection]
  case «90» =>
    change sourceChord half (rawFlatten (indexedDirection alpha (columnView j).1 (columnView j).2))
      (1+u*v) (u*v-1) (-(u+v)) 305 =
      sourceChord half (direction alpha (columnView j).1 (columnView j).2)
        (1+u*v) (u*v-1) (-(u+v)) 305
    rw [rawFlatten_indexedDirection]
  case «91» =>
    change sourceChord half (rawFlatten (indexedDirection alpha (columnView j).1 (columnView j).2))
      (1+u*v) (u*v-1) (-(u+v)) 307 =
      sourceChord half (direction alpha (columnView j).1 (columnView j).2)
        (1+u*v) (u*v-1) (-(u+v)) 307
    rw [rawFlatten_indexedDirection]
  case «92» =>
    change sourceChord half (rawFlatten (indexedDirection alpha (columnView j).1 (columnView j).2))
      (1+u*v) (u*v-1) (-(u+v)) 311 =
      sourceChord half (direction alpha (columnView j).1 (columnView j).2)
        (1+u*v) (u*v-1) (-(u+v)) 311
    rw [rawFlatten_indexedDirection]
  case «93» =>
    change sourceChord half (rawFlatten (indexedDirection alpha (columnView j).1 (columnView j).2))
      (1+u*v) (u*v-1) (-(u+v)) 313 =
      sourceChord half (direction alpha (columnView j).1 (columnView j).2)
        (1+u*v) (u*v-1) (-(u+v)) 313
    rw [rawFlatten_indexedDirection]
  case «94» =>
    change sourceChord half (rawFlatten (indexedDirection alpha (columnView j).1 (columnView j).2))
      (1+u*v) (u*v-1) (-(u+v)) 315 =
      sourceChord half (direction alpha (columnView j).1 (columnView j).2)
        (1+u*v) (u*v-1) (-(u+v)) 315
    rw [rawFlatten_indexedDirection]
  case «95» =>
    change sourceChord half (rawFlatten (indexedDirection alpha (columnView j).1 (columnView j).2))
      (1+u*v) (u*v-1) (-(u+v)) 317 =
      sourceChord half (direction alpha (columnView j).1 (columnView j).2)
        (1+u*v) (u*v-1) (-(u+v)) 317
    rw [rawFlatten_indexedDirection]
  case «96» =>
    change sourceChord half (rawFlatten (indexedDirection alpha (columnView j).1 (columnView j).2))
      (1+u*v) (u*v-1) (-(u+v)) 319 =
      sourceChord half (direction alpha (columnView j).1 (columnView j).2)
        (1+u*v) (u*v-1) (-(u+v)) 319
    rw [rawFlatten_indexedDirection]
  case «97» =>
    change sourceChord half (rawFlatten (indexedDirection alpha (columnView j).1 (columnView j).2))
      (1+u*v) (u*v-1) (-(u+v)) 321 =
      sourceChord half (direction alpha (columnView j).1 (columnView j).2)
        (1+u*v) (u*v-1) (-(u+v)) 321
    rw [rawFlatten_indexedDirection]
  case «98» =>
    change sourceChord half (rawFlatten (indexedDirection alpha (columnView j).1 (columnView j).2))
      (1+u*v) (u*v-1) (-(u+v)) 323 =
      sourceChord half (direction alpha (columnView j).1 (columnView j).2)
        (1+u*v) (u*v-1) (-(u+v)) 323
    rw [rawFlatten_indexedDirection]
  case «99» =>
    change sourceChord half (rawFlatten (indexedDirection alpha (columnView j).1 (columnView j).2))
      (1+u*v) (u*v-1) (-(u+v)) 325 =
      sourceChord half (direction alpha (columnView j).1 (columnView j).2)
        (1+u*v) (u*v-1) (-(u+v)) 325
    rw [rawFlatten_indexedDirection]
  case «100» =>
    change sourceChord half (rawFlatten (indexedDirection alpha (columnView j).1 (columnView j).2))
      (1+u*v) (u*v-1) (-(u+v)) 327 =
      sourceChord half (direction alpha (columnView j).1 (columnView j).2)
        (1+u*v) (u*v-1) (-(u+v)) 327
    rw [rawFlatten_indexedDirection]
  case «101» =>
    change sourceChord half (rawFlatten (indexedDirection alpha (columnView j).1 (columnView j).2))
      (1+u*v) (u*v-1) (-(u+v)) 329 =
      sourceChord half (direction alpha (columnView j).1 (columnView j).2)
        (1+u*v) (u*v-1) (-(u+v)) 329
    rw [rawFlatten_indexedDirection]
  case «102» =>
    change sourceChord half (rawFlatten (indexedDirection alpha (columnView j).1 (columnView j).2))
      (1+u*v) (u*v-1) (-(u+v)) 331 =
      sourceChord half (direction alpha (columnView j).1 (columnView j).2)
        (1+u*v) (u*v-1) (-(u+v)) 331
    rw [rawFlatten_indexedDirection]
  case «103» =>
    change sourceChord half (rawFlatten (indexedDirection alpha (columnView j).1 (columnView j).2))
      (1+u*v) (u*v-1) (-(u+v)) 333 =
      sourceChord half (direction alpha (columnView j).1 (columnView j).2)
        (1+u*v) (u*v-1) (-(u+v)) 333
    rw [rawFlatten_indexedDirection]
  case «104» =>
    change sourceChord half (rawFlatten (indexedDirection alpha (columnView j).1 (columnView j).2))
      (1+u*v) (u*v-1) (-(u+v)) 335 =
      sourceChord half (direction alpha (columnView j).1 (columnView j).2)
        (1+u*v) (u*v-1) (-(u+v)) 335
    rw [rawFlatten_indexedDirection]
  case «105» =>
    change sourceChord half (rawFlatten (indexedDirection alpha (columnView j).1 (columnView j).2))
      (1+u*v) (u*v-1) (-(u+v)) 337 =
      sourceChord half (direction alpha (columnView j).1 (columnView j).2)
        (1+u*v) (u*v-1) (-(u+v)) 337
    rw [rawFlatten_indexedDirection]
  case «106» =>
    change sourceChord half (rawFlatten (indexedDirection alpha (columnView j).1 (columnView j).2))
      (1+u*v) (u*v-1) (-(u+v)) 339 =
      sourceChord half (direction alpha (columnView j).1 (columnView j).2)
        (1+u*v) (u*v-1) (-(u+v)) 339
    rw [rawFlatten_indexedDirection]
  case «107» =>
    change sourceChord half (rawFlatten (indexedDirection alpha (columnView j).1 (columnView j).2))
      (1+u*v) (u*v-1) (-(u+v)) 341 =
      sourceChord half (direction alpha (columnView j).1 (columnView j).2)
        (1+u*v) (u*v-1) (-(u+v)) 341
    rw [rawFlatten_indexedDirection]
  case «108» =>
    change sourceChord half (rawFlatten (indexedDirection alpha (columnView j).1 (columnView j).2))
      (1+u*v) (u*v-1) (-(u+v)) 343 =
      sourceChord half (direction alpha (columnView j).1 (columnView j).2)
        (1+u*v) (u*v-1) (-(u+v)) 343
    rw [rawFlatten_indexedDirection]
  case «109» =>
    change sourceChord half (rawFlatten (indexedDirection alpha (columnView j).1 (columnView j).2))
      (1+u*v) (u*v-1) (-(u+v)) 345 =
      sourceChord half (direction alpha (columnView j).1 (columnView j).2)
        (1+u*v) (u*v-1) (-(u+v)) 345
    rw [rawFlatten_indexedDirection]
  case «110» =>
    change sourceChord half (rawFlatten (indexedDirection alpha (columnView j).1 (columnView j).2))
      (1+u*v) (u*v-1) (-(u+v)) 347 =
      sourceChord half (direction alpha (columnView j).1 (columnView j).2)
        (1+u*v) (u*v-1) (-(u+v)) 347
    rw [rawFlatten_indexedDirection]
  case «111» =>
    change sourceChord half (rawFlatten (indexedDirection alpha (columnView j).1 (columnView j).2))
      (1+u*v) (u*v-1) (-(u+v)) 349 =
      sourceChord half (direction alpha (columnView j).1 (columnView j).2)
        (1+u*v) (u*v-1) (-(u+v)) 349
    rw [rawFlatten_indexedDirection]
  case «112» =>
    change sourceChord half (rawFlatten (indexedDirection alpha (columnView j).1 (columnView j).2))
      (1+u*v) (u*v-1) (-(u+v)) 351 =
      sourceChord half (direction alpha (columnView j).1 (columnView j).2)
        (1+u*v) (u*v-1) (-(u+v)) 351
    rw [rawFlatten_indexedDirection]
  case «113» =>
    change sourceChord half (rawFlatten (indexedDirection alpha (columnView j).1 (columnView j).2))
      (1+u*v) (u*v-1) (-(u+v)) 353 =
      sourceChord half (direction alpha (columnView j).1 (columnView j).2)
        (1+u*v) (u*v-1) (-(u+v)) 353
    rw [rawFlatten_indexedDirection]
  case «114» =>
    change sourceChord half (rawFlatten (indexedDirection alpha (columnView j).1 (columnView j).2))
      (1+u*v) (u*v-1) (-(u+v)) 355 =
      sourceChord half (direction alpha (columnView j).1 (columnView j).2)
        (1+u*v) (u*v-1) (-(u+v)) 355
    rw [rawFlatten_indexedDirection]
  case «115» =>
    change sourceChord half (rawFlatten (indexedDirection alpha (columnView j).1 (columnView j).2))
      (1+u*v) (u*v-1) (-(u+v)) 357 =
      sourceChord half (direction alpha (columnView j).1 (columnView j).2)
        (1+u*v) (u*v-1) (-(u+v)) 357
    rw [rawFlatten_indexedDirection]
  case «116» =>
    change sourceChord half (rawFlatten (indexedDirection alpha (columnView j).1 (columnView j).2))
      (1+u*v) (u*v-1) (-(u+v)) 359 =
      sourceChord half (direction alpha (columnView j).1 (columnView j).2)
        (1+u*v) (u*v-1) (-(u+v)) 359
    rw [rawFlatten_indexedDirection]
  case «117» =>
    change sourceChord half (rawFlatten (indexedDirection alpha (columnView j).1 (columnView j).2))
      (1+u*v) (u*v-1) (-(u+v)) 361 =
      sourceChord half (direction alpha (columnView j).1 (columnView j).2)
        (1+u*v) (u*v-1) (-(u+v)) 361
    rw [rawFlatten_indexedDirection]
  case «118» =>
    change sourceChord half (rawFlatten (indexedDirection alpha (columnView j).1 (columnView j).2))
      (1+u*v) (u*v-1) (-(u+v)) 365 =
      sourceChord half (direction alpha (columnView j).1 (columnView j).2)
        (1+u*v) (u*v-1) (-(u+v)) 365
    rw [rawFlatten_indexedDirection]
  case «119» =>
    change sourceChord half (rawFlatten (indexedDirection alpha (columnView j).1 (columnView j).2))
      (1+u*v) (u*v-1) (-(u+v)) 367 =
      sourceChord half (direction alpha (columnView j).1 (columnView j).2)
        (1+u*v) (u*v-1) (-(u+v)) 367
    rw [rawFlatten_indexedDirection]
  case «120» =>
    change sourceChord half (rawFlatten (indexedDirection alpha (columnView j).1 (columnView j).2))
      (1+u*v) (u*v-1) (-(u+v)) 370 =
      sourceChord half (direction alpha (columnView j).1 (columnView j).2)
        (1+u*v) (u*v-1) (-(u+v)) 370
    rw [rawFlatten_indexedDirection]
  case «121» =>
    change sourceChord half (rawFlatten (indexedDirection alpha (columnView j).1 (columnView j).2))
      (1+u*v) (u*v-1) (-(u+v)) 372 =
      sourceChord half (direction alpha (columnView j).1 (columnView j).2)
        (1+u*v) (u*v-1) (-(u+v)) 372
    rw [rawFlatten_indexedDirection]
  case «122» =>
    change sourceChord half (rawFlatten (indexedDirection alpha (columnView j).1 (columnView j).2))
      (1+u*v) (u*v-1) (-(u+v)) 374 =
      sourceChord half (direction alpha (columnView j).1 (columnView j).2)
        (1+u*v) (u*v-1) (-(u+v)) 374
    rw [rawFlatten_indexedDirection]
  case «123» =>
    change sourceChord half (rawFlatten (indexedDirection alpha (columnView j).1 (columnView j).2))
      (1+u*v) (u*v-1) (-(u+v)) 376 =
      sourceChord half (direction alpha (columnView j).1 (columnView j).2)
        (1+u*v) (u*v-1) (-(u+v)) 376
    rw [rawFlatten_indexedDirection]
  case «124» =>
    change sourceChord half (rawFlatten (indexedDirection alpha (columnView j).1 (columnView j).2))
      (1+u*v) (u*v-1) (-(u+v)) 378 =
      sourceChord half (direction alpha (columnView j).1 (columnView j).2)
        (1+u*v) (u*v-1) (-(u+v)) 378
    rw [rawFlatten_indexedDirection]
  case «125» =>
    change sourceChord half (rawFlatten (indexedDirection alpha (columnView j).1 (columnView j).2))
      (1+u*v) (u*v-1) (-(u+v)) 380 =
      sourceChord half (direction alpha (columnView j).1 (columnView j).2)
        (1+u*v) (u*v-1) (-(u+v)) 380
    rw [rawFlatten_indexedDirection]
  case «126» =>
    change sourceChord half (rawFlatten (indexedDirection alpha (columnView j).1 (columnView j).2))
      (1+u*v) (u*v-1) (-(u+v)) 382 =
      sourceChord half (direction alpha (columnView j).1 (columnView j).2)
        (1+u*v) (u*v-1) (-(u+v)) 382
    rw [rawFlatten_indexedDirection]
  case «127» =>
    change sourceChord half (rawFlatten (indexedDirection alpha (columnView j).1 (columnView j).2))
      (1+u*v) (u*v-1) (-(u+v)) 499 =
      sourceChord half (direction alpha (columnView j).1 (columnView j).2)
        (1+u*v) (u*v-1) (-(u+v)) 499
    rw [rawFlatten_indexedDirection]
  case «128» =>
    change sourceChord half (rawFlatten (indexedDirection alpha (columnView j).1 (columnView j).2))
      (1+u*v) (u*v-1) (-(u+v)) 501 =
      sourceChord half (direction alpha (columnView j).1 (columnView j).2)
        (1+u*v) (u*v-1) (-(u+v)) 501
    rw [rawFlatten_indexedDirection]
  case «129» =>
    change sourceChord half (rawFlatten (indexedDirection alpha (columnView j).1 (columnView j).2))
      (1+u*v) (u*v-1) (-(u+v)) 503 =
      sourceChord half (direction alpha (columnView j).1 (columnView j).2)
        (1+u*v) (u*v-1) (-(u+v)) 503
    rw [rawFlatten_indexedDirection]
  case «130» =>
    change sourceChord half (rawFlatten (indexedDirection alpha (columnView j).1 (columnView j).2))
      (1+u*v) (u*v-1) (-(u+v)) 505 =
      sourceChord half (direction alpha (columnView j).1 (columnView j).2)
        (1+u*v) (u*v-1) (-(u+v)) 505
    rw [rawFlatten_indexedDirection]
  case «131» =>
    change sourceChord half (rawFlatten (indexedDirection alpha (columnView j).1 (columnView j).2))
      (1+u*v) (u*v-1) (-(u+v)) 507 =
      sourceChord half (direction alpha (columnView j).1 (columnView j).2)
        (1+u*v) (u*v-1) (-(u+v)) 507
    rw [rawFlatten_indexedDirection]
  case «132» =>
    change sourceChord half (rawFlatten (indexedDirection alpha (columnView j).1 (columnView j).2))
      (1+u*v) (u*v-1) (-(u+v)) 509 =
      sourceChord half (direction alpha (columnView j).1 (columnView j).2)
        (1+u*v) (u*v-1) (-(u+v)) 509
    rw [rawFlatten_indexedDirection]
  case «133» =>
    change sourceChord half (rawFlatten (indexedDirection alpha (columnView j).1 (columnView j).2))
      (1+u*v) (u*v-1) (-(u+v)) 511 =
      sourceChord half (direction alpha (columnView j).1 (columnView j).2)
        (1+u*v) (u*v-1) (-(u+v)) 511
    rw [rawFlatten_indexedDirection]
  case «134» =>
    change sourceChord half (rawFlatten (indexedDirection alpha (columnView j).1 (columnView j).2))
      (1+u*v) (u*v-1) (-(u+v)) 626 =
      sourceChord half (direction alpha (columnView j).1 (columnView j).2)
        (1+u*v) (u*v-1) (-(u+v)) 626
    rw [rawFlatten_indexedDirection]
  case «135» =>
    change sourceChord half (rawFlatten (indexedDirection alpha (columnView j).1 (columnView j).2))
      (1+u*v) (u*v-1) (-(u+v)) 628 =
      sourceChord half (direction alpha (columnView j).1 (columnView j).2)
        (1+u*v) (u*v-1) (-(u+v)) 628
    rw [rawFlatten_indexedDirection]
  case «136» =>
    change sourceChord half (rawFlatten (indexedDirection alpha (columnView j).1 (columnView j).2))
      (1+u*v) (u*v-1) (-(u+v)) 630 =
      sourceChord half (direction alpha (columnView j).1 (columnView j).2)
        (1+u*v) (u*v-1) (-(u+v)) 630
    rw [rawFlatten_indexedDirection]
  case «137» =>
    change sourceChord half (rawFlatten (indexedDirection alpha (columnView j).1 (columnView j).2))
      (1+u*v) (u*v-1) (-(u+v)) 632 =
      sourceChord half (direction alpha (columnView j).1 (columnView j).2)
        (1+u*v) (u*v-1) (-(u+v)) 632
    rw [rawFlatten_indexedDirection]
  case «138» =>
    change sourceChord half (rawFlatten (indexedDirection alpha (columnView j).1 (columnView j).2))
      (1+u*v) (u*v-1) (-(u+v)) 634 =
      sourceChord half (direction alpha (columnView j).1 (columnView j).2)
        (1+u*v) (u*v-1) (-(u+v)) 634
    rw [rawFlatten_indexedDirection]
  case «139» =>
    change sourceChord half (rawFlatten (indexedDirection alpha (columnView j).1 (columnView j).2))
      (1+u*v) (u*v-1) (-(u+v)) 636 =
      sourceChord half (direction alpha (columnView j).1 (columnView j).2)
        (1+u*v) (u*v-1) (-(u+v)) 636
    rw [rawFlatten_indexedDirection]
  case «140» =>
    change sourceChord half (rawFlatten (indexedDirection alpha (columnView j).1 (columnView j).2))
      (1+u*v) (u*v-1) (-(u+v)) 638 =
      sourceChord half (direction alpha (columnView j).1 (columnView j).2)
        (1+u*v) (u*v-1) (-(u+v)) 638
    rw [rawFlatten_indexedDirection]
  case «141» =>
    change sourceChord half (rawFlatten (indexedDirection alpha (columnView j).1 (columnView j).2))
      (1+u*v) (u*v-1) (-(u+v)) 639 =
      sourceChord half (direction alpha (columnView j).1 (columnView j).2)
        (1+u*v) (u*v-1) (-(u+v)) 639
    rw [rawFlatten_indexedDirection]
  case «142» =>
    change sourceChord half (rawFlatten (indexedDirection alpha (columnView j).1 (columnView j).2))
      (1+u*v) (u*v-1) (-(u+v)) 755 =
      sourceChord half (direction alpha (columnView j).1 (columnView j).2)
        (1+u*v) (u*v-1) (-(u+v)) 755
    rw [rawFlatten_indexedDirection]
  case «143» =>
    change sourceChord half (rawFlatten (indexedDirection alpha (columnView j).1 (columnView j).2))
      (1+u*v) (u*v-1) (-(u+v)) 757 =
      sourceChord half (direction alpha (columnView j).1 (columnView j).2)
        (1+u*v) (u*v-1) (-(u+v)) 757
    rw [rawFlatten_indexedDirection]
  case «144» =>
    change sourceChord half (rawFlatten (indexedDirection alpha (columnView j).1 (columnView j).2))
      (1+u*v) (u*v-1) (-(u+v)) 759 =
      sourceChord half (direction alpha (columnView j).1 (columnView j).2)
        (1+u*v) (u*v-1) (-(u+v)) 759
    rw [rawFlatten_indexedDirection]
  case «145» =>
    change sourceChord half (rawFlatten (indexedDirection alpha (columnView j).1 (columnView j).2))
      (1+u*v) (u*v-1) (-(u+v)) 761 =
      sourceChord half (direction alpha (columnView j).1 (columnView j).2)
        (1+u*v) (u*v-1) (-(u+v)) 761
    rw [rawFlatten_indexedDirection]
  case «146» =>
    change sourceChord half (rawFlatten (indexedDirection alpha (columnView j).1 (columnView j).2))
      (1+u*v) (u*v-1) (-(u+v)) 763 =
      sourceChord half (direction alpha (columnView j).1 (columnView j).2)
        (1+u*v) (u*v-1) (-(u+v)) 763
    rw [rawFlatten_indexedDirection]
  case «147» =>
    change sourceChord half (rawFlatten (indexedDirection alpha (columnView j).1 (columnView j).2))
      (1+u*v) (u*v-1) (-(u+v)) 765 =
      sourceChord half (direction alpha (columnView j).1 (columnView j).2)
        (1+u*v) (u*v-1) (-(u+v)) 765
    rw [rawFlatten_indexedDirection]
  case «148» =>
    change sourceChord half (rawFlatten (indexedDirection alpha (columnView j).1 (columnView j).2))
      (1+u*v) (u*v-1) (-(u+v)) 766 =
      sourceChord half (direction alpha (columnView j).1 (columnView j).2)
        (1+u*v) (u*v-1) (-(u+v)) 766
    rw [rawFlatten_indexedDirection]
  case «149» =>
    change sourceChord half (rawFlatten (indexedDirection alpha (columnView j).1 (columnView j).2))
      (1+u*v) (u*v-1) (-(u+v)) 882 =
      sourceChord half (direction alpha (columnView j).1 (columnView j).2)
        (1+u*v) (u*v-1) (-(u+v)) 882
    rw [rawFlatten_indexedDirection]
  case «150» =>
    change sourceChord half (rawFlatten (indexedDirection alpha (columnView j).1 (columnView j).2))
      (1+u*v) (u*v-1) (-(u+v)) 884 =
      sourceChord half (direction alpha (columnView j).1 (columnView j).2)
        (1+u*v) (u*v-1) (-(u+v)) 884
    rw [rawFlatten_indexedDirection]
  case «151» =>
    change sourceChord half (rawFlatten (indexedDirection alpha (columnView j).1 (columnView j).2))
      (1+u*v) (u*v-1) (-(u+v)) 886 =
      sourceChord half (direction alpha (columnView j).1 (columnView j).2)
        (1+u*v) (u*v-1) (-(u+v)) 886
    rw [rawFlatten_indexedDirection]
  case «152» =>
    change sourceChord half (rawFlatten (indexedDirection alpha (columnView j).1 (columnView j).2))
      (1+u*v) (u*v-1) (-(u+v)) 888 =
      sourceChord half (direction alpha (columnView j).1 (columnView j).2)
        (1+u*v) (u*v-1) (-(u+v)) 888
    rw [rawFlatten_indexedDirection]
  case «153» =>
    change sourceChord half (rawFlatten (indexedDirection alpha (columnView j).1 (columnView j).2))
      (1+u*v) (u*v-1) (-(u+v)) 890 =
      sourceChord half (direction alpha (columnView j).1 (columnView j).2)
        (1+u*v) (u*v-1) (-(u+v)) 890
    rw [rawFlatten_indexedDirection]
  case «154» =>
    change sourceChord half (rawFlatten (indexedDirection alpha (columnView j).1 (columnView j).2))
      (1+u*v) (u*v-1) (-(u+v)) 892 =
      sourceChord half (direction alpha (columnView j).1 (columnView j).2)
        (1+u*v) (u*v-1) (-(u+v)) 892
    rw [rawFlatten_indexedDirection]
  case «155» =>
    change sourceChord half (rawFlatten (indexedDirection alpha (columnView j).1 (columnView j).2))
      (1+u*v) (u*v-1) (-(u+v)) 894 =
      sourceChord half (direction alpha (columnView j).1 (columnView j).2)
        (1+u*v) (u*v-1) (-(u+v)) 894
    rw [rawFlatten_indexedDirection]
  case «156» =>
    change sourceChord half (rawFlatten (indexedDirection alpha (columnView j).1 (columnView j).2))
      (1+u*v) (u*v-1) (-(u+v)) 900 =
      sourceChord half (direction alpha (columnView j).1 (columnView j).2)
        (1+u*v) (u*v-1) (-(u+v)) 900
    rw [rawFlatten_indexedDirection]
  case «157» =>
    change sourceChord half (rawFlatten (indexedDirection alpha (columnView j).1 (columnView j).2))
      (1+u*v) (u*v-1) (-(u+v)) 902 =
      sourceChord half (direction alpha (columnView j).1 (columnView j).2)
        (1+u*v) (u*v-1) (-(u+v)) 902
    rw [rawFlatten_indexedDirection]
  case «158» =>
    change sourceChord half (rawFlatten (indexedDirection alpha (columnView j).1 (columnView j).2))
      (1+u*v) (u*v-1) (-(u+v)) 904 =
      sourceChord half (direction alpha (columnView j).1 (columnView j).2)
        (1+u*v) (u*v-1) (-(u+v)) 904
    rw [rawFlatten_indexedDirection]
  case «159» =>
    change sourceChord half (rawFlatten (indexedDirection alpha (columnView j).1 (columnView j).2))
      (1+u*v) (u*v-1) (-(u+v)) 906 =
      sourceChord half (direction alpha (columnView j).1 (columnView j).2)
        (1+u*v) (u*v-1) (-(u+v)) 906
    rw [rawFlatten_indexedDirection]
  case «160» =>
    change sourceChord half (rawFlatten (indexedDirection alpha (columnView j).1 (columnView j).2))
      (1+u*v) (u*v-1) (-(u+v)) 908 =
      sourceChord half (direction alpha (columnView j).1 (columnView j).2)
        (1+u*v) (u*v-1) (-(u+v)) 908
    rw [rawFlatten_indexedDirection]
  case «161» =>
    change sourceChord half (rawFlatten (indexedDirection alpha (columnView j).1 (columnView j).2))
      (1+u*v) (u*v-1) (-(u+v)) 910 =
      sourceChord half (direction alpha (columnView j).1 (columnView j).2)
        (1+u*v) (u*v-1) (-(u+v)) 910
    rw [rawFlatten_indexedDirection]
  case «162» =>
    change sourceChord half (rawFlatten (indexedDirection alpha (columnView j).1 (columnView j).2))
      (1+u*v) (u*v-1) (-(u+v)) 912 =
      sourceChord half (direction alpha (columnView j).1 (columnView j).2)
        (1+u*v) (u*v-1) (-(u+v)) 912
    rw [rawFlatten_indexedDirection]
  case «163» =>
    change sourceChord half (rawFlatten (indexedDirection alpha (columnView j).1 (columnView j).2))
      (1+u*v) (u*v-1) (-(u+v)) 914 =
      sourceChord half (direction alpha (columnView j).1 (columnView j).2)
        (1+u*v) (u*v-1) (-(u+v)) 914
    rw [rawFlatten_indexedDirection]
  case «164» =>
    change sourceChord half (rawFlatten (indexedDirection alpha (columnView j).1 (columnView j).2))
      (1+u*v) (u*v-1) (-(u+v)) 916 =
      sourceChord half (direction alpha (columnView j).1 (columnView j).2)
        (1+u*v) (u*v-1) (-(u+v)) 916
    rw [rawFlatten_indexedDirection]
  case «165» =>
    change sourceChord half (rawFlatten (indexedDirection alpha (columnView j).1 (columnView j).2))
      (1+u*v) (u*v-1) (-(u+v)) 918 =
      sourceChord half (direction alpha (columnView j).1 (columnView j).2)
        (1+u*v) (u*v-1) (-(u+v)) 918
    rw [rawFlatten_indexedDirection]
  case «166» =>
    change sourceChord half (rawFlatten (indexedDirection alpha (columnView j).1 (columnView j).2))
      (1+u*v) (u*v-1) (-(u+v)) 920 =
      sourceChord half (direction alpha (columnView j).1 (columnView j).2)
        (1+u*v) (u*v-1) (-(u+v)) 920
    rw [rawFlatten_indexedDirection]
  case «167» =>
    change sourceChord half (rawFlatten (indexedDirection alpha (columnView j).1 (columnView j).2))
      (1+u*v) (u*v-1) (-(u+v)) 922 =
      sourceChord half (direction alpha (columnView j).1 (columnView j).2)
        (1+u*v) (u*v-1) (-(u+v)) 922
    rw [rawFlatten_indexedDirection]
  case «168» =>
    change sourceChord half (rawFlatten (indexedDirection alpha (columnView j).1 (columnView j).2))
      (1+u*v) (u*v-1) (-(u+v)) 924 =
      sourceChord half (direction alpha (columnView j).1 (columnView j).2)
        (1+u*v) (u*v-1) (-(u+v)) 924
    rw [rawFlatten_indexedDirection]
  case «169» =>
    change sourceChord half (rawFlatten (indexedDirection alpha (columnView j).1 (columnView j).2))
      (1+u*v) (u*v-1) (-(u+v)) 926 =
      sourceChord half (direction alpha (columnView j).1 (columnView j).2)
        (1+u*v) (u*v-1) (-(u+v)) 926
    rw [rawFlatten_indexedDirection]
  case «170» =>
    change sourceChord half (rawFlatten (indexedDirection alpha (columnView j).1 (columnView j).2))
      (1+u*v) (u*v-1) (-(u+v)) 928 =
      sourceChord half (direction alpha (columnView j).1 (columnView j).2)
        (1+u*v) (u*v-1) (-(u+v)) 928
    rw [rawFlatten_indexedDirection]
  case «171» =>
    change sourceChord half (rawFlatten (indexedDirection alpha (columnView j).1 (columnView j).2))
      (1+u*v) (u*v-1) (-(u+v)) 930 =
      sourceChord half (direction alpha (columnView j).1 (columnView j).2)
        (1+u*v) (u*v-1) (-(u+v)) 930
    rw [rawFlatten_indexedDirection]
  case «172» =>
    change sourceChord half (rawFlatten (indexedDirection alpha (columnView j).1 (columnView j).2))
      (1+u*v) (u*v-1) (-(u+v)) 932 =
      sourceChord half (direction alpha (columnView j).1 (columnView j).2)
        (1+u*v) (u*v-1) (-(u+v)) 932
    rw [rawFlatten_indexedDirection]
  case «173» =>
    change sourceChord half (rawFlatten (indexedDirection alpha (columnView j).1 (columnView j).2))
      (1+u*v) (u*v-1) (-(u+v)) 934 =
      sourceChord half (direction alpha (columnView j).1 (columnView j).2)
        (1+u*v) (u*v-1) (-(u+v)) 934
    rw [rawFlatten_indexedDirection]
  case «174» =>
    change sourceChord half (rawFlatten (indexedDirection alpha (columnView j).1 (columnView j).2))
      (1+u*v) (u*v-1) (-(u+v)) 936 =
      sourceChord half (direction alpha (columnView j).1 (columnView j).2)
        (1+u*v) (u*v-1) (-(u+v)) 936
    rw [rawFlatten_indexedDirection]
  case «175» =>
    change sourceChord half (rawFlatten (indexedDirection alpha (columnView j).1 (columnView j).2))
      (1+u*v) (u*v-1) (-(u+v)) 938 =
      sourceChord half (direction alpha (columnView j).1 (columnView j).2)
        (1+u*v) (u*v-1) (-(u+v)) 938
    rw [rawFlatten_indexedDirection]
  case «176» =>
    change sourceChord half (rawFlatten (indexedDirection alpha (columnView j).1 (columnView j).2))
      (1+u*v) (u*v-1) (-(u+v)) 940 =
      sourceChord half (direction alpha (columnView j).1 (columnView j).2)
        (1+u*v) (u*v-1) (-(u+v)) 940
    rw [rawFlatten_indexedDirection]
  case «177» =>
    change sourceChord half (rawFlatten (indexedDirection alpha (columnView j).1 (columnView j).2))
      (1+u*v) (u*v-1) (-(u+v)) 942 =
      sourceChord half (direction alpha (columnView j).1 (columnView j).2)
        (1+u*v) (u*v-1) (-(u+v)) 942
    rw [rawFlatten_indexedDirection]
  case «178» =>
    change sourceChord half (rawFlatten (indexedDirection alpha (columnView j).1 (columnView j).2))
      (1+u*v) (u*v-1) (-(u+v)) 944 =
      sourceChord half (direction alpha (columnView j).1 (columnView j).2)
        (1+u*v) (u*v-1) (-(u+v)) 944
    rw [rawFlatten_indexedDirection]
  case «179» =>
    change sourceChord half (rawFlatten (indexedDirection alpha (columnView j).1 (columnView j).2))
      (1+u*v) (u*v-1) (-(u+v)) 948 =
      sourceChord half (direction alpha (columnView j).1 (columnView j).2)
        (1+u*v) (u*v-1) (-(u+v)) 948
    rw [rawFlatten_indexedDirection]
  case «180» =>
    change sourceChord half (rawFlatten (indexedDirection alpha (columnView j).1 (columnView j).2))
      (1+u*v) (u*v-1) (-(u+v)) 952 =
      sourceChord half (direction alpha (columnView j).1 (columnView j).2)
        (1+u*v) (u*v-1) (-(u+v)) 952
    rw [rawFlatten_indexedDirection]
  case «181» =>
    change sourceChord half (rawFlatten (indexedDirection alpha (columnView j).1 (columnView j).2))
      (1+u*v) (u*v-1) (-(u+v)) 954 =
      sourceChord half (direction alpha (columnView j).1 (columnView j).2)
        (1+u*v) (u*v-1) (-(u+v)) 954
    rw [rawFlatten_indexedDirection]
  case «182» =>
    change sourceChord half (rawFlatten (indexedDirection alpha (columnView j).1 (columnView j).2))
      (1+u*v) (u*v-1) (-(u+v)) 958 =
      sourceChord half (direction alpha (columnView j).1 (columnView j).2)
        (1+u*v) (u*v-1) (-(u+v)) 958
    rw [rawFlatten_indexedDirection]
  case «183» =>
    change sourceChord half (rawFlatten (indexedDirection alpha (columnView j).1 (columnView j).2))
      (1+u*v) (u*v-1) (-(u+v)) 960 =
      sourceChord half (direction alpha (columnView j).1 (columnView j).2)
        (1+u*v) (u*v-1) (-(u+v)) 960
    rw [rawFlatten_indexedDirection]
  case «184» =>
    change sourceChord half (rawFlatten (indexedDirection alpha (columnView j).1 (columnView j).2))
      (1+u*v) (u*v-1) (-(u+v)) 962 =
      sourceChord half (direction alpha (columnView j).1 (columnView j).2)
        (1+u*v) (u*v-1) (-(u+v)) 962
    rw [rawFlatten_indexedDirection]
  case «185» =>
    change sourceChord half (rawFlatten (indexedDirection alpha (columnView j).1 (columnView j).2))
      (1+u*v) (u*v-1) (-(u+v)) 964 =
      sourceChord half (direction alpha (columnView j).1 (columnView j).2)
        (1+u*v) (u*v-1) (-(u+v)) 964
    rw [rawFlatten_indexedDirection]
  case «186» =>
    change sourceChord half (rawFlatten (indexedDirection alpha (columnView j).1 (columnView j).2))
      (1+u*v) (u*v-1) (-(u+v)) 966 =
      sourceChord half (direction alpha (columnView j).1 (columnView j).2)
        (1+u*v) (u*v-1) (-(u+v)) 966
    rw [rawFlatten_indexedDirection]
  case «187» =>
    change sourceChord half (rawFlatten (indexedDirection alpha (columnView j).1 (columnView j).2))
      (1+u*v) (u*v-1) (-(u+v)) 968 =
      sourceChord half (direction alpha (columnView j).1 (columnView j).2)
        (1+u*v) (u*v-1) (-(u+v)) 968
    rw [rawFlatten_indexedDirection]
  case «188» =>
    change sourceChord half (rawFlatten (indexedDirection alpha (columnView j).1 (columnView j).2))
      (1+u*v) (u*v-1) (-(u+v)) 970 =
      sourceChord half (direction alpha (columnView j).1 (columnView j).2)
        (1+u*v) (u*v-1) (-(u+v)) 970
    rw [rawFlatten_indexedDirection]
  case «189» =>
    change sourceChord half (rawFlatten (indexedDirection alpha (columnView j).1 (columnView j).2))
      (1+u*v) (u*v-1) (-(u+v)) 972 =
      sourceChord half (direction alpha (columnView j).1 (columnView j).2)
        (1+u*v) (u*v-1) (-(u+v)) 972
    rw [rawFlatten_indexedDirection]
  case «190» =>
    change sourceChord half (rawFlatten (indexedDirection alpha (columnView j).1 (columnView j).2))
      (1+u*v) (u*v-1) (-(u+v)) 974 =
      sourceChord half (direction alpha (columnView j).1 (columnView j).2)
        (1+u*v) (u*v-1) (-(u+v)) 974
    rw [rawFlatten_indexedDirection]
  case «191» =>
    change sourceChord half (rawFlatten (indexedDirection alpha (columnView j).1 (columnView j).2))
      (1+u*v) (u*v-1) (-(u+v)) 976 =
      sourceChord half (direction alpha (columnView j).1 (columnView j).2)
        (1+u*v) (u*v-1) (-(u+v)) 976
    rw [rawFlatten_indexedDirection]
  case «192» =>
    change sourceChord half (rawFlatten (indexedDirection alpha (columnView j).1 (columnView j).2))
      (1+u*v) (u*v-1) (-(u+v)) 978 =
      sourceChord half (direction alpha (columnView j).1 (columnView j).2)
        (1+u*v) (u*v-1) (-(u+v)) 978
    rw [rawFlatten_indexedDirection]
  case «193» =>
    change sourceChord half (rawFlatten (indexedDirection alpha (columnView j).1 (columnView j).2))
      (1+u*v) (u*v-1) (-(u+v)) 980 =
      sourceChord half (direction alpha (columnView j).1 (columnView j).2)
        (1+u*v) (u*v-1) (-(u+v)) 980
    rw [rawFlatten_indexedDirection]
  case «194» =>
    change sourceChord half (rawFlatten (indexedDirection alpha (columnView j).1 (columnView j).2))
      (1+u*v) (u*v-1) (-(u+v)) 982 =
      sourceChord half (direction alpha (columnView j).1 (columnView j).2)
        (1+u*v) (u*v-1) (-(u+v)) 982
    rw [rawFlatten_indexedDirection]
  case «195» =>
    change sourceChord half (rawFlatten (indexedDirection alpha (columnView j).1 (columnView j).2))
      (1+u*v) (u*v-1) (-(u+v)) 984 =
      sourceChord half (direction alpha (columnView j).1 (columnView j).2)
        (1+u*v) (u*v-1) (-(u+v)) 984
    rw [rawFlatten_indexedDirection]
  case «196» =>
    change sourceChord half (rawFlatten (indexedDirection alpha (columnView j).1 (columnView j).2))
      (1+u*v) (u*v-1) (-(u+v)) 986 =
      sourceChord half (direction alpha (columnView j).1 (columnView j).2)
        (1+u*v) (u*v-1) (-(u+v)) 986
    rw [rawFlatten_indexedDirection]
  case «197» =>
    change sourceChord half (rawFlatten (indexedDirection alpha (columnView j).1 (columnView j).2))
      (1+u*v) (u*v-1) (-(u+v)) 988 =
      sourceChord half (direction alpha (columnView j).1 (columnView j).2)
        (1+u*v) (u*v-1) (-(u+v)) 988
    rw [rawFlatten_indexedDirection]
  case «198» =>
    change sourceChord half (rawFlatten (indexedDirection alpha (columnView j).1 (columnView j).2))
      (1+u*v) (u*v-1) (-(u+v)) 990 =
      sourceChord half (direction alpha (columnView j).1 (columnView j).2)
        (1+u*v) (u*v-1) (-(u+v)) 990
    rw [rawFlatten_indexedDirection]
  case «199» =>
    change sourceChord half (rawFlatten (indexedDirection alpha (columnView j).1 (columnView j).2))
      (1+u*v) (u*v-1) (-(u+v)) 992 =
      sourceChord half (direction alpha (columnView j).1 (columnView j).2)
        (1+u*v) (u*v-1) (-(u+v)) 992
    rw [rawFlatten_indexedDirection]
  case «200» =>
    change sourceChord half (rawFlatten (indexedDirection alpha (columnView j).1 (columnView j).2))
      (1+u*v) (u*v-1) (-(u+v)) 994 =
      sourceChord half (direction alpha (columnView j).1 (columnView j).2)
        (1+u*v) (u*v-1) (-(u+v)) 994
    rw [rawFlatten_indexedDirection]
  case «201» =>
    change sourceChord half (rawFlatten (indexedDirection alpha (columnView j).1 (columnView j).2))
      (1+u*v) (u*v-1) (-(u+v)) 996 =
      sourceChord half (direction alpha (columnView j).1 (columnView j).2)
        (1+u*v) (u*v-1) (-(u+v)) 996
    rw [rawFlatten_indexedDirection]
  case «202» =>
    change sourceChord half (rawFlatten (indexedDirection alpha (columnView j).1 (columnView j).2))
      (1+u*v) (u*v-1) (-(u+v)) 998 =
      sourceChord half (direction alpha (columnView j).1 (columnView j).2)
        (1+u*v) (u*v-1) (-(u+v)) 998
    rw [rawFlatten_indexedDirection]
  case «203» =>
    change sourceChord half (rawFlatten (indexedDirection alpha (columnView j).1 (columnView j).2))
      (1+u*v) (u*v-1) (-(u+v)) 1000 =
      sourceChord half (direction alpha (columnView j).1 (columnView j).2)
        (1+u*v) (u*v-1) (-(u+v)) 1000
    rw [rawFlatten_indexedDirection]
  case «204» =>
    change sourceChord half (rawFlatten (indexedDirection alpha (columnView j).1 (columnView j).2))
      (1+u*v) (u*v-1) (-(u+v)) 1002 =
      sourceChord half (direction alpha (columnView j).1 (columnView j).2)
        (1+u*v) (u*v-1) (-(u+v)) 1002
    rw [rawFlatten_indexedDirection]
  case «205» =>
    change sourceChord half (rawFlatten (indexedDirection alpha (columnView j).1 (columnView j).2))
      (1+u*v) (u*v-1) (-(u+v)) 1004 =
      sourceChord half (direction alpha (columnView j).1 (columnView j).2)
        (1+u*v) (u*v-1) (-(u+v)) 1004
    rw [rawFlatten_indexedDirection]
  case «206» =>
    change sourceChord half (rawFlatten (indexedDirection alpha (columnView j).1 (columnView j).2))
      (1+u*v) (u*v-1) (-(u+v)) 1006 =
      sourceChord half (direction alpha (columnView j).1 (columnView j).2)
        (1+u*v) (u*v-1) (-(u+v)) 1006
    rw [rawFlatten_indexedDirection]
  case «207» =>
    change sourceChord half (rawFlatten (indexedDirection alpha (columnView j).1 (columnView j).2))
      (1+u*v) (u*v-1) (-(u+v)) 1008 =
      sourceChord half (direction alpha (columnView j).1 (columnView j).2)
        (1+u*v) (u*v-1) (-(u+v)) 1008
    rw [rawFlatten_indexedDirection]
  case «208» =>
    change sourceChord half (rawFlatten (indexedDirection alpha (columnView j).1 (columnView j).2))
      (1+u*v) (u*v-1) (-(u+v)) 1011 =
      sourceChord half (direction alpha (columnView j).1 (columnView j).2)
        (1+u*v) (u*v-1) (-(u+v)) 1011
    rw [rawFlatten_indexedDirection]
  case «209» =>
    change sourceChord half (rawFlatten (indexedDirection alpha (columnView j).1 (columnView j).2))
      (1+u*v) (u*v-1) (-(u+v)) 1013 =
      sourceChord half (direction alpha (columnView j).1 (columnView j).2)
        (1+u*v) (u*v-1) (-(u+v)) 1013
    rw [rawFlatten_indexedDirection]
  case «210» =>
    change sourceChord half (rawFlatten (indexedDirection alpha (columnView j).1 (columnView j).2))
      (1+u*v) (u*v-1) (-(u+v)) 1015 =
      sourceChord half (direction alpha (columnView j).1 (columnView j).2)
        (1+u*v) (u*v-1) (-(u+v)) 1015
    rw [rawFlatten_indexedDirection]
  case «211» =>
    change sourceChord half (rawFlatten (indexedDirection alpha (columnView j).1 (columnView j).2))
      (1+u*v) (u*v-1) (-(u+v)) 1017 =
      sourceChord half (direction alpha (columnView j).1 (columnView j).2)
        (1+u*v) (u*v-1) (-(u+v)) 1017
    rw [rawFlatten_indexedDirection]
  case «212» =>
    change sourceChord half (rawFlatten (indexedDirection alpha (columnView j).1 (columnView j).2))
      (1+u*v) (u*v-1) (-(u+v)) 1019 =
      sourceChord half (direction alpha (columnView j).1 (columnView j).2)
        (1+u*v) (u*v-1) (-(u+v)) 1019
    rw [rawFlatten_indexedDirection]
  case «213» =>
    change sourceChord half (rawFlatten (indexedDirection alpha (columnView j).1 (columnView j).2))
      (1+u*v) (u*v-1) (-(u+v)) 1022 =
      sourceChord half (direction alpha (columnView j).1 (columnView j).2)
        (1+u*v) (u*v-1) (-(u+v)) 1022
    rw [rawFlatten_indexedDirection]

#print axioms activeCodes_length
#print axioms activeCodeView_bounds
#print axioms literalSourceMatrix_active_entry
end
end AspisV8R19.R801LiteralActiveEntries
