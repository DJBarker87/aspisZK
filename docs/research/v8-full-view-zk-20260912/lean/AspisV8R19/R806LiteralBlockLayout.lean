import Mathlib.Data.Fintype.Card
import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 800000
namespace AspisV8R19.R806LiteralBlockLayout

-- Literal index tables only: no field arithmetic or certificate inversion is evaluated.
def blockSize (k : Fin 41) : Nat :=
  match k.val with
  | 0 => 6
  | 1 => 1
  | 2 => 3
  | 3 => 8
  | 4 => 16
  | 5 => 1
  | 6 => 39
  | 7 => 2
  | 8 => 8
  | 9 => 16
  | 10 => 1
  | 11 => 4
  | 12 => 16
  | 13 => 4
  | 14 => 1
  | 15 => 4
  | 16 => 2
  | 17 => 1
  | 18 => 2
  | 19 => 4
  | 20 => 2
  | 21 => 1
  | 22 => 8
  | 23 => 2
  | 24 => 2
  | 25 => 2
  | 26 => 1
  | 27 => 4
  | 28 => 2
  | 29 => 1
  | 30 => 2
  | 31 => 2
  | 32 => 8
  | 33 => 8
  | 34 => 4
  | 35 => 2
  | 36 => 3
  | 37 => 4
  | 38 => 8
  | 39 => 16
  | _ => 1

def blockOffset (k : Fin 41) : Nat :=
  match k.val with
  | 0 => 0
  | 1 => 6
  | 2 => 7
  | 3 => 10
  | 4 => 18
  | 5 => 34
  | 6 => 35
  | 7 => 74
  | 8 => 76
  | 9 => 84
  | 10 => 100
  | 11 => 101
  | 12 => 105
  | 13 => 121
  | 14 => 125
  | 15 => 126
  | 16 => 130
  | 17 => 132
  | 18 => 133
  | 19 => 135
  | 20 => 139
  | 21 => 141
  | 22 => 142
  | 23 => 150
  | 24 => 152
  | 25 => 154
  | 26 => 156
  | 27 => 157
  | 28 => 161
  | 29 => 163
  | 30 => 164
  | 31 => 166
  | 32 => 168
  | 33 => 176
  | 34 => 184
  | 35 => 188
  | 36 => 190
  | 37 => 193
  | 38 => 197
  | 39 => 205
  | _ => 221

def blockLabel (i : Fin 222) : Fin 41 :=
  match i.val with
  | 0 => 0
  | 1 => 0
  | 2 => 0
  | 3 => 0
  | 4 => 0
  | 5 => 0
  | 6 => 1
  | 7 => 2
  | 8 => 2
  | 9 => 2
  | 10 => 3
  | 11 => 3
  | 12 => 3
  | 13 => 3
  | 14 => 3
  | 15 => 3
  | 16 => 3
  | 17 => 3
  | 18 => 4
  | 19 => 4
  | 20 => 4
  | 21 => 4
  | 22 => 4
  | 23 => 4
  | 24 => 4
  | 25 => 4
  | 26 => 4
  | 27 => 4
  | 28 => 4
  | 29 => 4
  | 30 => 4
  | 31 => 4
  | 32 => 4
  | 33 => 4
  | 34 => 5
  | 35 => 6
  | 36 => 6
  | 37 => 6
  | 38 => 6
  | 39 => 6
  | 40 => 6
  | 41 => 6
  | 42 => 6
  | 43 => 6
  | 44 => 6
  | 45 => 6
  | 46 => 6
  | 47 => 6
  | 48 => 6
  | 49 => 6
  | 50 => 6
  | 51 => 6
  | 52 => 6
  | 53 => 6
  | 54 => 6
  | 55 => 6
  | 56 => 6
  | 57 => 6
  | 58 => 6
  | 59 => 6
  | 60 => 6
  | 61 => 6
  | 62 => 6
  | 63 => 6
  | 64 => 6
  | 65 => 6
  | 66 => 6
  | 67 => 6
  | 68 => 6
  | 69 => 6
  | 70 => 6
  | 71 => 6
  | 72 => 6
  | 73 => 6
  | 74 => 7
  | 75 => 7
  | 76 => 8
  | 77 => 8
  | 78 => 8
  | 79 => 8
  | 80 => 8
  | 81 => 8
  | 82 => 8
  | 83 => 8
  | 84 => 9
  | 85 => 9
  | 86 => 9
  | 87 => 9
  | 88 => 9
  | 89 => 9
  | 90 => 9
  | 91 => 9
  | 92 => 9
  | 93 => 9
  | 94 => 9
  | 95 => 9
  | 96 => 9
  | 97 => 9
  | 98 => 9
  | 99 => 9
  | 100 => 10
  | 101 => 11
  | 102 => 11
  | 103 => 11
  | 104 => 11
  | 105 => 12
  | 106 => 12
  | 107 => 12
  | 108 => 12
  | 109 => 12
  | 110 => 12
  | 111 => 12
  | 112 => 12
  | 113 => 12
  | 114 => 12
  | 115 => 12
  | 116 => 12
  | 117 => 12
  | 118 => 12
  | 119 => 12
  | 120 => 12
  | 121 => 13
  | 122 => 13
  | 123 => 13
  | 124 => 13
  | 125 => 14
  | 126 => 15
  | 127 => 15
  | 128 => 15
  | 129 => 15
  | 130 => 16
  | 131 => 16
  | 132 => 17
  | 133 => 18
  | 134 => 18
  | 135 => 19
  | 136 => 19
  | 137 => 19
  | 138 => 19
  | 139 => 20
  | 140 => 20
  | 141 => 21
  | 142 => 22
  | 143 => 22
  | 144 => 22
  | 145 => 22
  | 146 => 22
  | 147 => 22
  | 148 => 22
  | 149 => 22
  | 150 => 23
  | 151 => 23
  | 152 => 24
  | 153 => 24
  | 154 => 25
  | 155 => 25
  | 156 => 26
  | 157 => 27
  | 158 => 27
  | 159 => 27
  | 160 => 27
  | 161 => 28
  | 162 => 28
  | 163 => 29
  | 164 => 30
  | 165 => 30
  | 166 => 31
  | 167 => 31
  | 168 => 32
  | 169 => 32
  | 170 => 32
  | 171 => 32
  | 172 => 32
  | 173 => 32
  | 174 => 32
  | 175 => 32
  | 176 => 33
  | 177 => 33
  | 178 => 33
  | 179 => 33
  | 180 => 33
  | 181 => 33
  | 182 => 33
  | 183 => 33
  | 184 => 34
  | 185 => 34
  | 186 => 34
  | 187 => 34
  | 188 => 35
  | 189 => 35
  | 190 => 36
  | 191 => 36
  | 192 => 36
  | 193 => 37
  | 194 => 37
  | 195 => 37
  | 196 => 37
  | 197 => 38
  | 198 => 38
  | 199 => 38
  | 200 => 38
  | 201 => 38
  | 202 => 38
  | 203 => 38
  | 204 => 38
  | 205 => 39
  | 206 => 39
  | 207 => 39
  | 208 => 39
  | 209 => 39
  | 210 => 39
  | 211 => 39
  | 212 => 39
  | 213 => 39
  | 214 => 39
  | 215 => 39
  | 216 => 39
  | 217 => 39
  | 218 => 39
  | 219 => 39
  | 220 => 39
  | _ => 40

theorem blockSize_pos (k : Fin 41) : 0 < blockSize k := by revert k; decide

theorem block_end_bound (k : Fin 41) : blockOffset k + blockSize k ≤ 222 := by
  revert k
  decide

theorem blockLabel_bounds (i : Fin 222) (k : Fin 41) :
    blockLabel i = k ↔ blockOffset k ≤ i.val ∧ i.val < blockOffset k + blockSize k := by
  revert i k
  decide

def flatIndex (k : Fin 41) (t : Fin (blockSize k)) : Fin 222 :=
  ⟨blockOffset k + t.val, by have := block_end_bound k; have := t.isLt; omega⟩

theorem blockLabel_flatIndex (k : Fin 41) (t : Fin (blockSize k)) :
    blockLabel (flatIndex k t) = k := by
  apply (blockLabel_bounds _ _).mpr
  simp only [flatIndex, Fin.val_mk]
  have := t.isLt
  omega

def fiberEquiv (k : Fin 41) : Fin (blockSize k) ≃ {i : Fin 222 // blockLabel i = k} where
  toFun t := ⟨flatIndex k t, blockLabel_flatIndex k t⟩
  invFun i := ⟨i.val.val - blockOffset k, by
    have := (blockLabel_bounds i.val k).mp i.property
    omega⟩
  left_inv t := by
    apply Fin.ext
    simp only [flatIndex, Fin.val_mk]
    omega
  right_inv i := by
    apply Subtype.ext
    apply Fin.ext
    simp only [flatIndex, Fin.val_mk]
    have := (blockLabel_bounds i.val k).mp i.property
    omega

#print axioms blockSize_pos
#print axioms block_end_bound
#print axioms blockLabel_bounds
#print axioms blockLabel_flatIndex
#print axioms fiberEquiv
end AspisV8R19.R806LiteralBlockLayout
