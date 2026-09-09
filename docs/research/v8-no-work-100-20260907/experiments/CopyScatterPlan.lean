import CopyScatterCells30
import CopyScatterCells55
import CopyScatterCells80
namespace AspisV8.CopyScatter
variable {K : Type*} [CommRing K]
def originalCells0 (h:Fin 64→K) (w:Fin 43→K) : Fin 25→K := ![
(0:K) + w 0 * (h 63) + w 0 * (h 4),
(0:K) + w 0 * (h 57),
(0:K) + w 0 * (h 63) + w 0 * (h 57) + w 0 * (h 58) + w 0 * (h 59) + w 0 * (h 60) + w 0 * (h 61) + w 0 * (h 62),
(0:K) + w 0 * (h 63),
(0:K) + w 0 * (h 63) + w 0 * (h 57) + w 0 * (h 58) + w 0 * (h 59) + w 0 * (h 60) + w 0 * (h 61) + w 0 * (h 62),
(0:K) + w 0 * (h 63) + w 0 * (h 57) + w 0 * (h 58) + w 0 * (h 59) + w 0 * (h 60) + w 0 * (h 61) + w 0 * (h 62),
(0:K) + w 0 * (h 1) + w 0 * (h 2) + w 0 * (h 25) + w 1 * (h 27) + w 1 * (h 28) + w 0 * (h 30) + w 0 * (h 31) + w 0 * (h 0) + w 1 * (h 32) + w 1 * (h 29) + w 3 * (h 33) + w 4 * (h 34) + w 5 * (h 35) + w 6 * (h 36) + w 7 * (h 37) + w 8 * (h 38) + w 9 * (h 39) + w 10 * (h 40) + w 11 * (h 41) + w 12 * (h 42) + w 13 * (h 43) + w 14 * (h 44) + w 15 * (h 45) + w 16 * (h 46) + w 17 * (h 47) + w 18 * (h 48) + w 19 * (h 49) + w 20 * (h 50) + w 21 * (h 51) + w 22 * (h 52) + w 0 * (h 3) + w 0 * (h 4) + w 0 * (h 5) + w 0 * (h 6) + w 0 * (h 7) + w 0 * (h 8) + w 0 * (h 9) + w 0 * (h 10) + w 0 * (h 11) + w 0 * (h 12) + w 0 * (h 13) + w 0 * (h 14) + w 0 * (h 15) + w 0 * (h 16) + w 0 * (h 17) + w 0 * (h 18) + w 0 * (h 19) + w 0 * (h 20) + w 0 * (h 21) + w 0 * (h 22) + w 0 * (h 23) + w 0 * (h 24) + w 0 * (h 54) + w 0 * (h 55),
(0:K) + w 0 * (h 0) + w 0 * (h 2) + w 0 * (h 3) + w 1 * (h 28) + w 0 * (h 31),
(0:K) + w 0 * (h 57) + w 0 * (h 58) + w 0 * (h 59) + w 0 * (h 60) + w 0 * (h 61) + w 0 * (h 62),
(0:K) + w 0 * (h 57) + w 0 * (h 58) + w 0 * (h 59) + w 0 * (h 60) + w 0 * (h 61) + w 0 * (h 62),
(0:K) + w 0 * (h 57) + w 0 * (h 58) + w 0 * (h 59) + w 0 * (h 60) + w 0 * (h 61) + w 0 * (h 62),
(0:K) + w 0 * (h 57) + w 0 * (h 58) + w 0 * (h 59) + w 0 * (h 60) + w 0 * (h 61) + w 0 * (h 62),
(0:K) + w 2 * (h 32) + w 23 * (h 33) + w 24 * (h 34) + w 25 * (h 35) + w 26 * (h 36) + w 27 * (h 37) + w 28 * (h 38) + w 29 * (h 39) + w 30 * (h 40) + w 31 * (h 41) + w 32 * (h 42) + w 33 * (h 43) + w 34 * (h 44) + w 35 * (h 45) + w 36 * (h 46) + w 37 * (h 47) + w 38 * (h 48) + w 39 * (h 49) + w 40 * (h 50) + w 41 * (h 51) + w 42 * (h 52),
(0:K) + w 0 * (h 2),
(0:K) + w 0 * (h 57) + w 0 * (h 58) + w 0 * (h 59) + w 0 * (h 60) + w 0 * (h 61) + w 0 * (h 62),
(0:K) + w 0 * (h 2) + w 0 * (h 3) + w 0 * (h 26) + w 1 * (h 28) + w 1 * (h 29) + w 0 * (h 31) + w 0 * (h 32) + w 0 * (h 63) + w 0 * (h 33) + w 23 * (h 34) + w 24 * (h 35) + w 25 * (h 36) + w 26 * (h 37) + w 27 * (h 38) + w 28 * (h 39) + w 29 * (h 40) + w 30 * (h 41) + w 31 * (h 42) + w 32 * (h 43) + w 33 * (h 44) + w 34 * (h 45) + w 35 * (h 46) + w 36 * (h 47) + w 37 * (h 48) + w 38 * (h 49) + w 39 * (h 50) + w 40 * (h 51) + w 41 * (h 52) + w 42 * (h 53) + w 0 * (h 4) + w 0 * (h 5) + w 0 * (h 6) + w 0 * (h 7) + w 0 * (h 8) + w 0 * (h 9) + w 0 * (h 10) + w 0 * (h 11) + w 0 * (h 12) + w 0 * (h 13) + w 0 * (h 14) + w 0 * (h 15) + w 0 * (h 16) + w 0 * (h 17) + w 0 * (h 18) + w 0 * (h 19) + w 0 * (h 20) + w 0 * (h 21) + w 0 * (h 22) + w 0 * (h 23) + w 0 * (h 24) + w 0 * (h 54) + w 0 * (h 55) + w 0 * (h 56),
(0:K) + w 0 * (h 57) + w 0 * (h 58) + w 0 * (h 59) + w 0 * (h 60) + w 0 * (h 61) + w 0 * (h 62),
(0:K) + w 1 * (h 63),
(0:K) + w 0 * (h 63),
(0:K) + w 0 * (h 57) + w 0 * (h 58) + w 0 * (h 59) + w 0 * (h 60) + w 0 * (h 61) + w 0 * (h 62),
(0:K) + w 0 * (h 63),
(0:K) + w 0 * (h 63),
(0:K) + w 0 * (h 63) + w 0 * (h 57) + w 0 * (h 58) + w 0 * (h 59) + w 0 * (h 60) + w 0 * (h 61) + w 0 * (h 62),
(0:K) + w 1 * (h 63),
(0:K) + w 0 * (h 1) + w 0 * (h 25) + w 0 * (h 26) + w 1 * (h 33) + w 3 * (h 34) + w 4 * (h 35) + w 5 * (h 36) + w 6 * (h 37) + w 7 * (h 38) + w 8 * (h 39) + w 9 * (h 40) + w 10 * (h 41) + w 11 * (h 42) + w 12 * (h 43) + w 13 * (h 44) + w 14 * (h 45) + w 15 * (h 46) + w 16 * (h 47) + w 17 * (h 48) + w 18 * (h 49) + w 19 * (h 50) + w 20 * (h 51) + w 21 * (h 52) + w 22 * (h 53) + w 0 * (h 4) + w 0 * (h 5) + w 0 * (h 6) + w 0 * (h 7) + w 0 * (h 8) + w 0 * (h 9) + w 0 * (h 10) + w 0 * (h 11) + w 0 * (h 12) + w 0 * (h 13) + w 0 * (h 14) + w 0 * (h 15) + w 0 * (h 16) + w 0 * (h 17) + w 0 * (h 18) + w 0 * (h 19) + w 0 * (h 20) + w 0 * (h 21) + w 0 * (h 22) + w 0 * (h 23) + w 0 * (h 24) + w 0 * (h 54) + w 0 * (h 55) + w 0 * (h 56)]
def originalCells25 (h:Fin 64→K) (w:Fin 43→K) : Fin 25→K := ![
(0:K) + w 0 * (h 57) + w 0 * (h 58) + w 0 * (h 59) + w 0 * (h 60) + w 0 * (h 61) + w 0 * (h 62),
(0:K) + w 0 * (h 63),
(0:K) + w 0 * (h 63),
(0:K) + w 0 * (h 63),
(0:K) + w 0 * (h 26) + w 2 * (h 33),
(0:K) + h 1 + h 2 + h 25 + h 27 + h 28 + h 30 + h 31,
(0:K) + h 57 + h 58 + h 59 + h 60 + h 61 + h 62,
(0:K) + h 57 + h 58 + h 59 + h 60 + h 61 + h 62,
(0:K) + h 57 + h 58 + h 59 + h 60 + h 61 + h 62,
(0:K) + h 0 + h 32 + h 29 + h 33 + h 34 + h 35 + h 36 + h 37 + h 38 + h 39 + h 40 + h 41 + h 42 + h 43 + h 44 + h 45 + h 46 + h 47 + h 48 + h 49 + h 50 + h 51 + h 52 + h 3 + h 4 + h 5 + h 6 + h 7 + h 8 + h 9 + h 10 + h 11 + h 12 + h 13 + h 14 + h 15 + h 16 + h 17 + h 18 + h 19 + h 20 + h 21 + h 22 + h 23 + h 24 + h 54 + h 55,
(0:K) + h 0,
(0:K) + h 57 + h 58 + h 59 + h 60 + h 61 + h 62,
(0:K) + h 2,
(0:K) + h 3,
(0:K) + h 57,
(0:K) + h 28 + h 31,
(0:K) + h 63,
(0:K) + h 63,
(0:K) + h 63,
(0:K) + h 63,
(0:K) + h 4,
(0:K) + h 63,
(0:K) + h 32 + h 33 + h 34 + h 35 + h 36 + h 37 + h 38 + h 39 + h 40 + h 41 + h 42 + h 43 + h 44 + h 45 + h 46 + h 47 + h 48 + h 49 + h 50 + h 51 + h 52,
(0:K) + h 2,
(0:K) + h 57 + h 58 + h 59 + h 60 + h 61 + h 62]
def originalCells50 (h:Fin 64→K) (w:Fin 43→K) : Fin 23→K := ![
(0:K) + h 57 + h 58 + h 59 + h 60 + h 61 + h 62,
(0:K) + h 57 + h 58 + h 59 + h 60 + h 61 + h 62,
(0:K) + h 57 + h 58 + h 59 + h 60 + h 61 + h 62,
(0:K) + h 2 + h 3 + h 26 + h 28 + h 29 + h 31 + h 32,
(0:K) + h 1 + h 25 + h 33 + h 34 + h 35 + h 36 + h 37 + h 38 + h 39 + h 40 + h 41 + h 42 + h 43 + h 44 + h 45 + h 46 + h 47 + h 48 + h 49 + h 50 + h 51 + h 52 + h 53 + h 4 + h 5 + h 6 + h 7 + h 8 + h 9 + h 10 + h 11 + h 12 + h 13 + h 14 + h 15 + h 16 + h 17 + h 18 + h 19 + h 20 + h 21 + h 22 + h 23 + h 24 + h 54 + h 55 + h 56,
(0:K) + h 26,
(0:K) + h 63,
(0:K) + h 63,
(0:K) + h 63,
(0:K) + h 63,
(0:K) + h 63,
(0:K) + h 33 + h 34 + h 35 + h 36 + h 37 + h 38 + h 39 + h 40 + h 41 + h 42 + h 43 + h 44 + h 45 + h 46 + h 47 + h 48 + h 49 + h 50 + h 51 + h 52 + h 53 + h 4 + h 5 + h 6 + h 7 + h 8 + h 9 + h 10 + h 11 + h 12 + h 13 + h 14 + h 15 + h 16 + h 17 + h 18 + h 19 + h 20 + h 21 + h 22 + h 23 + h 24 + h 54 + h 55 + h 56,
(0:K) + h 63,
(0:K) + h 63,
(0:K) + h 57 + h 58 + h 59 + h 60 + h 61 + h 62,
(0:K) + h 57 + h 58 + h 59 + h 60 + h 61 + h 62,
(0:K) + h 57 + h 58 + h 59 + h 60 + h 61 + h 62,
(0:K) + h 57 + h 58 + h 59 + h 60 + h 61 + h 62,
(0:K) + h 33,
(0:K) + h 26,
(0:K) + h 63,
(0:K) + h 63,
(0:K) + h 63]
def originalCells (h:Fin 64→K) (w:Fin 43→K) (i:Fin 73) : K :=
  if h0:i.val<25 then originalCells0 h w ⟨i.val,h0⟩
  else if h1:i.val<50 then originalCells25 h w ⟨i.val-25,by omega⟩
  else originalCells50 h w ⟨i.val-50,by omega⟩
def planCells0 (h:Fin 64→K) (w:Fin 43→K) : Fin 25→K := ![
w 0 * (h 4 + h 63),
w 0 * (h 57),
w 0 * (node41 h),
w 0 * (h 63),
w 0 * (node41 h),
w 0 * (node41 h),
w 0 * (node29 h + node52 h + node54 h) + w 1 * (h 27 + h 32 + node51 h) + w 3 * (h 33) + w 4 * (h 34) + w 5 * (h 35) + w 6 * (h 36) + w 7 * (h 37) + w 8 * (h 38) + w 9 * (h 39) + w 10 * (h 40) + w 11 * (h 41) + w 12 * (h 42) + w 13 * (h 43) + w 14 * (h 44) + w 15 * (h 45) + w 16 * (h 46) + w 17 * (h 47) + w 18 * (h 48) + w 19 * (h 49) + w 20 * (h 50) + w 21 * (h 51) + w 22 * (h 52),
w 0 * (h 0 + node29 h) + w 1 * (h 28),
w 0 * (node4 h),
w 0 * (node4 h),
w 0 * (node4 h),
w 0 * (node4 h),
w 2 * (h 32) + w 23 * (h 33) + w 24 * (h 34) + w 25 * (h 35) + w 26 * (h 36) + w 27 * (h 37) + w 28 * (h 38) + w 29 * (h 39) + w 30 * (h 40) + w 31 * (h 41) + w 32 * (h 42) + w 33 * (h 43) + w 34 * (h 44) + w 35 * (h 45) + w 36 * (h 46) + w 37 * (h 47) + w 38 * (h 48) + w 39 * (h 49) + w 40 * (h 50) + w 41 * (h 51) + w 42 * (h 52),
w 0 * (h 2),
w 0 * (node4 h),
w 0 * (h 33 + h 63 + node40 h + node57 h) + w 1 * (node51 h) + w 23 * (h 34) + w 24 * (h 35) + w 25 * (h 36) + w 26 * (h 37) + w 27 * (h 38) + w 28 * (h 39) + w 29 * (h 40) + w 30 * (h 41) + w 31 * (h 42) + w 32 * (h 43) + w 33 * (h 44) + w 34 * (h 45) + w 35 * (h 46) + w 36 * (h 47) + w 37 * (h 48) + w 38 * (h 49) + w 39 * (h 50) + w 40 * (h 51) + w 41 * (h 52) + w 42 * (h 53),
w 0 * (node4 h),
w 1 * (h 63),
w 0 * (h 63),
w 0 * (node4 h),
w 0 * (h 63),
w 0 * (h 63),
w 0 * (node41 h),
w 1 * (h 63),
w 0 * (h 26 + node28 h + node40 h) + w 1 * (h 33) + w 3 * (h 34) + w 4 * (h 35) + w 5 * (h 36) + w 6 * (h 37) + w 7 * (h 38) + w 8 * (h 39) + w 9 * (h 40) + w 10 * (h 41) + w 11 * (h 42) + w 12 * (h 43) + w 13 * (h 44) + w 14 * (h 45) + w 15 * (h 46) + w 16 * (h 47) + w 17 * (h 48) + w 18 * (h 49) + w 19 * (h 50) + w 20 * (h 51) + w 21 * (h 52) + w 22 * (h 53)]
def planCells25 (h:Fin 64→K) (w:Fin 43→K) : Fin 25→K := ![
w 0 * (node4 h),
w 0 * (h 63),
w 0 * (h 63),
w 0 * (h 63),
w 0 * (h 26) + w 2 * (h 33),
(h 27 + h 28 + node27 h + node54 h),
(node4 h),
(node4 h),
(node4 h),
(h 3 + h 29 + node52 h + node55 h),
(h 0),
(node4 h),
(h 2),
(h 3),
(h 57),
(h 28 + h 31),
(h 63),
(h 63),
(h 63),
(h 63),
(h 4),
(h 63),
(node55 h),
(h 2),
(node4 h)]
def planCells50 (h:Fin 64→K) (w:Fin 43→K) : Fin 23→K := ![
(node4 h),
(node4 h),
(node4 h),
(node51 h + node57 h),
(node28 h + node58 h),
(h 26),
(h 63),
(h 63),
(h 63),
(h 63),
(h 63),
(node58 h),
(h 63),
(h 63),
(node4 h),
(node4 h),
(node4 h),
(node4 h),
(h 33),
(h 26),
(h 63),
(h 63),
(h 63)]
def planCells (h:Fin 64→K) (w:Fin 43→K) (i:Fin 73) : K :=
  if h0:i.val<25 then planCells0 h w ⟨i.val,h0⟩
  else if h1:i.val<50 then planCells25 h w ⟨i.val-25,by omega⟩
  else planCells50 h w ⟨i.val-50,by omega⟩
theorem all_modified_cells (h:Fin 64→K) (w:Fin 43→K) : originalCells h w=planCells h w := by
  funext i
  fin_cases i
  · exact coordinate30 h w
  · exact coordinate31 h w
  · exact coordinate32 h w
  · exact coordinate33 h w
  · exact coordinate34 h w
  · exact coordinate35 h w
  · exact coordinate36 h w
  · exact coordinate37 h w
  · exact coordinate38 h w
  · exact coordinate39 h w
  · exact coordinate40 h w
  · exact coordinate41 h w
  · exact coordinate42 h w
  · exact coordinate43 h w
  · exact coordinate44 h w
  · exact coordinate45 h w
  · exact coordinate46 h w
  · exact coordinate47 h w
  · exact coordinate48 h w
  · exact coordinate49 h w
  · exact coordinate50 h w
  · exact coordinate51 h w
  · exact coordinate52 h w
  · exact coordinate53 h w
  · exact coordinate54 h w
  · exact coordinate55 h w
  · exact coordinate56 h w
  · exact coordinate57 h w
  · exact coordinate58 h w
  · exact coordinate59 h w
  · exact coordinate60 h w
  · exact coordinate61 h w
  · exact coordinate62 h w
  · exact coordinate63 h w
  · exact coordinate64 h w
  · exact coordinate65 h w
  · exact coordinate66 h w
  · exact coordinate67 h w
  · exact coordinate68 h w
  · exact coordinate69 h w
  · exact coordinate70 h w
  · exact coordinate71 h w
  · exact coordinate72 h w
  · exact coordinate73 h w
  · exact coordinate74 h w
  · exact coordinate75 h w
  · exact coordinate76 h w
  · exact coordinate77 h w
  · exact coordinate78 h w
  · exact coordinate79 h w
  · exact coordinate80 h w
  · exact coordinate81 h w
  · exact coordinate82 h w
  · exact coordinate83 h w
  · exact coordinate84 h w
  · exact coordinate85 h w
  · exact coordinate86 h w
  · exact coordinate87 h w
  · exact coordinate88 h w
  · exact coordinate89 h w
  · exact coordinate90 h w
  · exact coordinate91 h w
  · exact coordinate92 h w
  · exact coordinate93 h w
  · exact coordinate94 h w
  · exact coordinate95 h w
  · exact coordinate96 h w
  · exact coordinate97 h w
  · exact coordinate98 h w
  · exact coordinate99 h w
  · exact coordinate100 h w
  · exact coordinate101 h w
  · exact coordinate102 h w
#print axioms all_modified_cells
end AspisV8.CopyScatter
