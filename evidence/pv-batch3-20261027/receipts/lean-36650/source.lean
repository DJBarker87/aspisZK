import PV_B3_MaskSparseBit
namespace PV_B3_MaskSparseMarks
open Aeneas Aeneas.Std PV_B3_MaskSparseStep
set_option autoImplicit false
theorem mark0011 (m : Nat → U16) (k : Nat) :
    (mark m 11#usize k).val = if k = 0 then (m k).val ||| 2048 else (m k).val := by
  simpa only [show (11#usize).val = 11 from rfl] using
    PV_B3_MaskSparseBit.mark_value m 11#usize k
#print axioms mark0011
theorem mark0012 (m : Nat → U16) (k : Nat) :
    (mark m 12#usize k).val = if k = 0 then (m k).val ||| 4096 else (m k).val := by
  simpa only [show (12#usize).val = 12 from rfl] using
    PV_B3_MaskSparseBit.mark_value m 12#usize k
#print axioms mark0012
theorem mark0027 (m : Nat → U16) (k : Nat) :
    (mark m 27#usize k).val = if k = 1 then (m k).val ||| 2048 else (m k).val := by
  simpa only [show (27#usize).val = 27 from rfl] using
    PV_B3_MaskSparseBit.mark_value m 27#usize k
#print axioms mark0027
theorem mark0028 (m : Nat → U16) (k : Nat) :
    (mark m 28#usize k).val = if k = 1 then (m k).val ||| 4096 else (m k).val := by
  simpa only [show (28#usize).val = 28 from rfl] using
    PV_B3_MaskSparseBit.mark_value m 28#usize k
#print axioms mark0028
theorem mark0032 (m : Nat → U16) (k : Nat) :
    (mark m 32#usize k).val = if k = 2 then (m k).val ||| 1 else (m k).val := by
  simpa only [show (32#usize).val = 32 from rfl] using
    PV_B3_MaskSparseBit.mark_value m 32#usize k
#print axioms mark0032
theorem mark0043 (m : Nat → U16) (k : Nat) :
    (mark m 43#usize k).val = if k = 2 then (m k).val ||| 2048 else (m k).val := by
  simpa only [show (43#usize).val = 43 from rfl] using
    PV_B3_MaskSparseBit.mark_value m 43#usize k
#print axioms mark0043
theorem mark0044 (m : Nat → U16) (k : Nat) :
    (mark m 44#usize k).val = if k = 2 then (m k).val ||| 4096 else (m k).val := by
  simpa only [show (44#usize).val = 44 from rfl] using
    PV_B3_MaskSparseBit.mark_value m 44#usize k
#print axioms mark0044
theorem mark0048 (m : Nat → U16) (k : Nat) :
    (mark m 48#usize k).val = if k = 3 then (m k).val ||| 1 else (m k).val := by
  simpa only [show (48#usize).val = 48 from rfl] using
    PV_B3_MaskSparseBit.mark_value m 48#usize k
#print axioms mark0048
theorem mark0059 (m : Nat → U16) (k : Nat) :
    (mark m 59#usize k).val = if k = 3 then (m k).val ||| 2048 else (m k).val := by
  simpa only [show (59#usize).val = 59 from rfl] using
    PV_B3_MaskSparseBit.mark_value m 59#usize k
#print axioms mark0059
theorem mark0060 (m : Nat → U16) (k : Nat) :
    (mark m 60#usize k).val = if k = 3 then (m k).val ||| 4096 else (m k).val := by
  simpa only [show (60#usize).val = 60 from rfl] using
    PV_B3_MaskSparseBit.mark_value m 60#usize k
#print axioms mark0060
theorem mark0064 (m : Nat → U16) (k : Nat) :
    (mark m 64#usize k).val = if k = 4 then (m k).val ||| 1 else (m k).val := by
  simpa only [show (64#usize).val = 64 from rfl] using
    PV_B3_MaskSparseBit.mark_value m 64#usize k
#print axioms mark0064
theorem mark0075 (m : Nat → U16) (k : Nat) :
    (mark m 75#usize k).val = if k = 4 then (m k).val ||| 2048 else (m k).val := by
  simpa only [show (75#usize).val = 75 from rfl] using
    PV_B3_MaskSparseBit.mark_value m 75#usize k
#print axioms mark0075
theorem mark0076 (m : Nat → U16) (k : Nat) :
    (mark m 76#usize k).val = if k = 4 then (m k).val ||| 4096 else (m k).val := by
  simpa only [show (76#usize).val = 76 from rfl] using
    PV_B3_MaskSparseBit.mark_value m 76#usize k
#print axioms mark0076
theorem mark0080 (m : Nat → U16) (k : Nat) :
    (mark m 80#usize k).val = if k = 5 then (m k).val ||| 1 else (m k).val := by
  simpa only [show (80#usize).val = 80 from rfl] using
    PV_B3_MaskSparseBit.mark_value m 80#usize k
#print axioms mark0080
theorem mark0091 (m : Nat → U16) (k : Nat) :
    (mark m 91#usize k).val = if k = 5 then (m k).val ||| 2048 else (m k).val := by
  simpa only [show (91#usize).val = 91 from rfl] using
    PV_B3_MaskSparseBit.mark_value m 91#usize k
#print axioms mark0091
theorem mark0092 (m : Nat → U16) (k : Nat) :
    (mark m 92#usize k).val = if k = 5 then (m k).val ||| 4096 else (m k).val := by
  simpa only [show (92#usize).val = 92 from rfl] using
    PV_B3_MaskSparseBit.mark_value m 92#usize k
#print axioms mark0092
theorem mark0096 (m : Nat → U16) (k : Nat) :
    (mark m 96#usize k).val = if k = 6 then (m k).val ||| 1 else (m k).val := by
  simpa only [show (96#usize).val = 96 from rfl] using
    PV_B3_MaskSparseBit.mark_value m 96#usize k
#print axioms mark0096
theorem mark0107 (m : Nat → U16) (k : Nat) :
    (mark m 107#usize k).val = if k = 6 then (m k).val ||| 2048 else (m k).val := by
  simpa only [show (107#usize).val = 107 from rfl] using
    PV_B3_MaskSparseBit.mark_value m 107#usize k
#print axioms mark0107
theorem mark0108 (m : Nat → U16) (k : Nat) :
    (mark m 108#usize k).val = if k = 6 then (m k).val ||| 4096 else (m k).val := by
  simpa only [show (108#usize).val = 108 from rfl] using
    PV_B3_MaskSparseBit.mark_value m 108#usize k
#print axioms mark0108
theorem mark0112 (m : Nat → U16) (k : Nat) :
    (mark m 112#usize k).val = if k = 7 then (m k).val ||| 1 else (m k).val := by
  simpa only [show (112#usize).val = 112 from rfl] using
    PV_B3_MaskSparseBit.mark_value m 112#usize k
#print axioms mark0112
theorem mark0123 (m : Nat → U16) (k : Nat) :
    (mark m 123#usize k).val = if k = 7 then (m k).val ||| 2048 else (m k).val := by
  simpa only [show (123#usize).val = 123 from rfl] using
    PV_B3_MaskSparseBit.mark_value m 123#usize k
#print axioms mark0123
theorem mark0124 (m : Nat → U16) (k : Nat) :
    (mark m 124#usize k).val = if k = 7 then (m k).val ||| 4096 else (m k).val := by
  simpa only [show (124#usize).val = 124 from rfl] using
    PV_B3_MaskSparseBit.mark_value m 124#usize k
#print axioms mark0124
theorem mark0128 (m : Nat → U16) (k : Nat) :
    (mark m 128#usize k).val = if k = 8 then (m k).val ||| 1 else (m k).val := by
  simpa only [show (128#usize).val = 128 from rfl] using
    PV_B3_MaskSparseBit.mark_value m 128#usize k
#print axioms mark0128
theorem mark0139 (m : Nat → U16) (k : Nat) :
    (mark m 139#usize k).val = if k = 8 then (m k).val ||| 2048 else (m k).val := by
  simpa only [show (139#usize).val = 139 from rfl] using
    PV_B3_MaskSparseBit.mark_value m 139#usize k
#print axioms mark0139
theorem mark0140 (m : Nat → U16) (k : Nat) :
    (mark m 140#usize k).val = if k = 8 then (m k).val ||| 4096 else (m k).val := by
  simpa only [show (140#usize).val = 140 from rfl] using
    PV_B3_MaskSparseBit.mark_value m 140#usize k
#print axioms mark0140
theorem mark0144 (m : Nat → U16) (k : Nat) :
    (mark m 144#usize k).val = if k = 9 then (m k).val ||| 1 else (m k).val := by
  simpa only [show (144#usize).val = 144 from rfl] using
    PV_B3_MaskSparseBit.mark_value m 144#usize k
#print axioms mark0144
theorem mark0155 (m : Nat → U16) (k : Nat) :
    (mark m 155#usize k).val = if k = 9 then (m k).val ||| 2048 else (m k).val := by
  simpa only [show (155#usize).val = 155 from rfl] using
    PV_B3_MaskSparseBit.mark_value m 155#usize k
#print axioms mark0155
theorem mark0156 (m : Nat → U16) (k : Nat) :
    (mark m 156#usize k).val = if k = 9 then (m k).val ||| 4096 else (m k).val := by
  simpa only [show (156#usize).val = 156 from rfl] using
    PV_B3_MaskSparseBit.mark_value m 156#usize k
#print axioms mark0156
theorem mark0160 (m : Nat → U16) (k : Nat) :
    (mark m 160#usize k).val = if k = 10 then (m k).val ||| 1 else (m k).val := by
  simpa only [show (160#usize).val = 160 from rfl] using
    PV_B3_MaskSparseBit.mark_value m 160#usize k
#print axioms mark0160
theorem mark0171 (m : Nat → U16) (k : Nat) :
    (mark m 171#usize k).val = if k = 10 then (m k).val ||| 2048 else (m k).val := by
  simpa only [show (171#usize).val = 171 from rfl] using
    PV_B3_MaskSparseBit.mark_value m 171#usize k
#print axioms mark0171
theorem mark0172 (m : Nat → U16) (k : Nat) :
    (mark m 172#usize k).val = if k = 10 then (m k).val ||| 4096 else (m k).val := by
  simpa only [show (172#usize).val = 172 from rfl] using
    PV_B3_MaskSparseBit.mark_value m 172#usize k
#print axioms mark0172
theorem mark0176 (m : Nat → U16) (k : Nat) :
    (mark m 176#usize k).val = if k = 11 then (m k).val ||| 1 else (m k).val := by
  simpa only [show (176#usize).val = 176 from rfl] using
    PV_B3_MaskSparseBit.mark_value m 176#usize k
#print axioms mark0176
theorem mark0187 (m : Nat → U16) (k : Nat) :
    (mark m 187#usize k).val = if k = 11 then (m k).val ||| 2048 else (m k).val := by
  simpa only [show (187#usize).val = 187 from rfl] using
    PV_B3_MaskSparseBit.mark_value m 187#usize k
#print axioms mark0187
theorem mark0188 (m : Nat → U16) (k : Nat) :
    (mark m 188#usize k).val = if k = 11 then (m k).val ||| 4096 else (m k).val := by
  simpa only [show (188#usize).val = 188 from rfl] using
    PV_B3_MaskSparseBit.mark_value m 188#usize k
#print axioms mark0188
theorem mark0192 (m : Nat → U16) (k : Nat) :
    (mark m 192#usize k).val = if k = 12 then (m k).val ||| 1 else (m k).val := by
  simpa only [show (192#usize).val = 192 from rfl] using
    PV_B3_MaskSparseBit.mark_value m 192#usize k
#print axioms mark0192
theorem mark0203 (m : Nat → U16) (k : Nat) :
    (mark m 203#usize k).val = if k = 12 then (m k).val ||| 2048 else (m k).val := by
  simpa only [show (203#usize).val = 203 from rfl] using
    PV_B3_MaskSparseBit.mark_value m 203#usize k
#print axioms mark0203
theorem mark0204 (m : Nat → U16) (k : Nat) :
    (mark m 204#usize k).val = if k = 12 then (m k).val ||| 4096 else (m k).val := by
  simpa only [show (204#usize).val = 204 from rfl] using
    PV_B3_MaskSparseBit.mark_value m 204#usize k
#print axioms mark0204
theorem mark0208 (m : Nat → U16) (k : Nat) :
    (mark m 208#usize k).val = if k = 13 then (m k).val ||| 1 else (m k).val := by
  simpa only [show (208#usize).val = 208 from rfl] using
    PV_B3_MaskSparseBit.mark_value m 208#usize k
#print axioms mark0208
theorem mark0219 (m : Nat → U16) (k : Nat) :
    (mark m 219#usize k).val = if k = 13 then (m k).val ||| 2048 else (m k).val := by
  simpa only [show (219#usize).val = 219 from rfl] using
    PV_B3_MaskSparseBit.mark_value m 219#usize k
#print axioms mark0219
theorem mark0220 (m : Nat → U16) (k : Nat) :
    (mark m 220#usize k).val = if k = 13 then (m k).val ||| 4096 else (m k).val := by
  simpa only [show (220#usize).val = 220 from rfl] using
    PV_B3_MaskSparseBit.mark_value m 220#usize k
#print axioms mark0220
theorem mark0224 (m : Nat → U16) (k : Nat) :
    (mark m 224#usize k).val = if k = 14 then (m k).val ||| 1 else (m k).val := by
  simpa only [show (224#usize).val = 224 from rfl] using
    PV_B3_MaskSparseBit.mark_value m 224#usize k
#print axioms mark0224
theorem mark0235 (m : Nat → U16) (k : Nat) :
    (mark m 235#usize k).val = if k = 14 then (m k).val ||| 2048 else (m k).val := by
  simpa only [show (235#usize).val = 235 from rfl] using
    PV_B3_MaskSparseBit.mark_value m 235#usize k
#print axioms mark0235
theorem mark0236 (m : Nat → U16) (k : Nat) :
    (mark m 236#usize k).val = if k = 14 then (m k).val ||| 4096 else (m k).val := by
  simpa only [show (236#usize).val = 236 from rfl] using
    PV_B3_MaskSparseBit.mark_value m 236#usize k
#print axioms mark0236
theorem mark0240 (m : Nat → U16) (k : Nat) :
    (mark m 240#usize k).val = if k = 15 then (m k).val ||| 1 else (m k).val := by
  simpa only [show (240#usize).val = 240 from rfl] using
    PV_B3_MaskSparseBit.mark_value m 240#usize k
#print axioms mark0240
theorem mark0251 (m : Nat → U16) (k : Nat) :
    (mark m 251#usize k).val = if k = 15 then (m k).val ||| 2048 else (m k).val := by
  simpa only [show (251#usize).val = 251 from rfl] using
    PV_B3_MaskSparseBit.mark_value m 251#usize k
#print axioms mark0251
theorem mark0252 (m : Nat → U16) (k : Nat) :
    (mark m 252#usize k).val = if k = 15 then (m k).val ||| 4096 else (m k).val := by
  simpa only [show (252#usize).val = 252 from rfl] using
    PV_B3_MaskSparseBit.mark_value m 252#usize k
#print axioms mark0252
theorem mark0256 (m : Nat → U16) (k : Nat) :
    (mark m 256#usize k).val = if k = 16 then (m k).val ||| 1 else (m k).val := by
  simpa only [show (256#usize).val = 256 from rfl] using
    PV_B3_MaskSparseBit.mark_value m 256#usize k
#print axioms mark0256
theorem mark0267 (m : Nat → U16) (k : Nat) :
    (mark m 267#usize k).val = if k = 16 then (m k).val ||| 2048 else (m k).val := by
  simpa only [show (267#usize).val = 267 from rfl] using
    PV_B3_MaskSparseBit.mark_value m 267#usize k
#print axioms mark0267
theorem mark0268 (m : Nat → U16) (k : Nat) :
    (mark m 268#usize k).val = if k = 16 then (m k).val ||| 4096 else (m k).val := by
  simpa only [show (268#usize).val = 268 from rfl] using
    PV_B3_MaskSparseBit.mark_value m 268#usize k
#print axioms mark0268
theorem mark0272 (m : Nat → U16) (k : Nat) :
    (mark m 272#usize k).val = if k = 17 then (m k).val ||| 1 else (m k).val := by
  simpa only [show (272#usize).val = 272 from rfl] using
    PV_B3_MaskSparseBit.mark_value m 272#usize k
#print axioms mark0272
theorem mark0283 (m : Nat → U16) (k : Nat) :
    (mark m 283#usize k).val = if k = 17 then (m k).val ||| 2048 else (m k).val := by
  simpa only [show (283#usize).val = 283 from rfl] using
    PV_B3_MaskSparseBit.mark_value m 283#usize k
#print axioms mark0283
theorem mark0284 (m : Nat → U16) (k : Nat) :
    (mark m 284#usize k).val = if k = 17 then (m k).val ||| 4096 else (m k).val := by
  simpa only [show (284#usize).val = 284 from rfl] using
    PV_B3_MaskSparseBit.mark_value m 284#usize k
#print axioms mark0284
theorem mark0288 (m : Nat → U16) (k : Nat) :
    (mark m 288#usize k).val = if k = 18 then (m k).val ||| 1 else (m k).val := by
  simpa only [show (288#usize).val = 288 from rfl] using
    PV_B3_MaskSparseBit.mark_value m 288#usize k
#print axioms mark0288
theorem mark0299 (m : Nat → U16) (k : Nat) :
    (mark m 299#usize k).val = if k = 18 then (m k).val ||| 2048 else (m k).val := by
  simpa only [show (299#usize).val = 299 from rfl] using
    PV_B3_MaskSparseBit.mark_value m 299#usize k
#print axioms mark0299
theorem mark0300 (m : Nat → U16) (k : Nat) :
    (mark m 300#usize k).val = if k = 18 then (m k).val ||| 4096 else (m k).val := by
  simpa only [show (300#usize).val = 300 from rfl] using
    PV_B3_MaskSparseBit.mark_value m 300#usize k
#print axioms mark0300
theorem mark0304 (m : Nat → U16) (k : Nat) :
    (mark m 304#usize k).val = if k = 19 then (m k).val ||| 1 else (m k).val := by
  simpa only [show (304#usize).val = 304 from rfl] using
    PV_B3_MaskSparseBit.mark_value m 304#usize k
#print axioms mark0304
theorem mark0315 (m : Nat → U16) (k : Nat) :
    (mark m 315#usize k).val = if k = 19 then (m k).val ||| 2048 else (m k).val := by
  simpa only [show (315#usize).val = 315 from rfl] using
    PV_B3_MaskSparseBit.mark_value m 315#usize k
#print axioms mark0315
theorem mark0316 (m : Nat → U16) (k : Nat) :
    (mark m 316#usize k).val = if k = 19 then (m k).val ||| 4096 else (m k).val := by
  simpa only [show (316#usize).val = 316 from rfl] using
    PV_B3_MaskSparseBit.mark_value m 316#usize k
#print axioms mark0316
theorem mark0320 (m : Nat → U16) (k : Nat) :
    (mark m 320#usize k).val = if k = 20 then (m k).val ||| 1 else (m k).val := by
  simpa only [show (320#usize).val = 320 from rfl] using
    PV_B3_MaskSparseBit.mark_value m 320#usize k
#print axioms mark0320
theorem mark0331 (m : Nat → U16) (k : Nat) :
    (mark m 331#usize k).val = if k = 20 then (m k).val ||| 2048 else (m k).val := by
  simpa only [show (331#usize).val = 331 from rfl] using
    PV_B3_MaskSparseBit.mark_value m 331#usize k
#print axioms mark0331
theorem mark0332 (m : Nat → U16) (k : Nat) :
    (mark m 332#usize k).val = if k = 20 then (m k).val ||| 4096 else (m k).val := by
  simpa only [show (332#usize).val = 332 from rfl] using
    PV_B3_MaskSparseBit.mark_value m 332#usize k
#print axioms mark0332
theorem mark0336 (m : Nat → U16) (k : Nat) :
    (mark m 336#usize k).val = if k = 21 then (m k).val ||| 1 else (m k).val := by
  simpa only [show (336#usize).val = 336 from rfl] using
    PV_B3_MaskSparseBit.mark_value m 336#usize k
#print axioms mark0336
theorem mark0347 (m : Nat → U16) (k : Nat) :
    (mark m 347#usize k).val = if k = 21 then (m k).val ||| 2048 else (m k).val := by
  simpa only [show (347#usize).val = 347 from rfl] using
    PV_B3_MaskSparseBit.mark_value m 347#usize k
#print axioms mark0347
theorem mark0348 (m : Nat → U16) (k : Nat) :
    (mark m 348#usize k).val = if k = 21 then (m k).val ||| 4096 else (m k).val := by
  simpa only [show (348#usize).val = 348 from rfl] using
    PV_B3_MaskSparseBit.mark_value m 348#usize k
#print axioms mark0348
theorem mark0352 (m : Nat → U16) (k : Nat) :
    (mark m 352#usize k).val = if k = 22 then (m k).val ||| 1 else (m k).val := by
  simpa only [show (352#usize).val = 352 from rfl] using
    PV_B3_MaskSparseBit.mark_value m 352#usize k
#print axioms mark0352
theorem mark0363 (m : Nat → U16) (k : Nat) :
    (mark m 363#usize k).val = if k = 22 then (m k).val ||| 2048 else (m k).val := by
  simpa only [show (363#usize).val = 363 from rfl] using
    PV_B3_MaskSparseBit.mark_value m 363#usize k
#print axioms mark0363
theorem mark0364 (m : Nat → U16) (k : Nat) :
    (mark m 364#usize k).val = if k = 22 then (m k).val ||| 4096 else (m k).val := by
  simpa only [show (364#usize).val = 364 from rfl] using
    PV_B3_MaskSparseBit.mark_value m 364#usize k
#print axioms mark0364
theorem mark0368 (m : Nat → U16) (k : Nat) :
    (mark m 368#usize k).val = if k = 23 then (m k).val ||| 1 else (m k).val := by
  simpa only [show (368#usize).val = 368 from rfl] using
    PV_B3_MaskSparseBit.mark_value m 368#usize k
#print axioms mark0368
theorem mark0379 (m : Nat → U16) (k : Nat) :
    (mark m 379#usize k).val = if k = 23 then (m k).val ||| 2048 else (m k).val := by
  simpa only [show (379#usize).val = 379 from rfl] using
    PV_B3_MaskSparseBit.mark_value m 379#usize k
#print axioms mark0379
theorem mark0380 (m : Nat → U16) (k : Nat) :
    (mark m 380#usize k).val = if k = 23 then (m k).val ||| 4096 else (m k).val := by
  simpa only [show (380#usize).val = 380 from rfl] using
    PV_B3_MaskSparseBit.mark_value m 380#usize k
#print axioms mark0380
theorem mark0384 (m : Nat → U16) (k : Nat) :
    (mark m 384#usize k).val = if k = 24 then (m k).val ||| 1 else (m k).val := by
  simpa only [show (384#usize).val = 384 from rfl] using
    PV_B3_MaskSparseBit.mark_value m 384#usize k
#print axioms mark0384
theorem mark0395 (m : Nat → U16) (k : Nat) :
    (mark m 395#usize k).val = if k = 24 then (m k).val ||| 2048 else (m k).val := by
  simpa only [show (395#usize).val = 395 from rfl] using
    PV_B3_MaskSparseBit.mark_value m 395#usize k
#print axioms mark0395
theorem mark0396 (m : Nat → U16) (k : Nat) :
    (mark m 396#usize k).val = if k = 24 then (m k).val ||| 4096 else (m k).val := by
  simpa only [show (396#usize).val = 396 from rfl] using
    PV_B3_MaskSparseBit.mark_value m 396#usize k
#print axioms mark0396
theorem mark0411 (m : Nat → U16) (k : Nat) :
    (mark m 411#usize k).val = if k = 25 then (m k).val ||| 2048 else (m k).val := by
  simpa only [show (411#usize).val = 411 from rfl] using
    PV_B3_MaskSparseBit.mark_value m 411#usize k
#print axioms mark0411
theorem mark0412 (m : Nat → U16) (k : Nat) :
    (mark m 412#usize k).val = if k = 25 then (m k).val ||| 4096 else (m k).val := by
  simpa only [show (412#usize).val = 412 from rfl] using
    PV_B3_MaskSparseBit.mark_value m 412#usize k
#print axioms mark0412
theorem mark0416 (m : Nat → U16) (k : Nat) :
    (mark m 416#usize k).val = if k = 26 then (m k).val ||| 1 else (m k).val := by
  simpa only [show (416#usize).val = 416 from rfl] using
    PV_B3_MaskSparseBit.mark_value m 416#usize k
#print axioms mark0416
theorem mark0428 (m : Nat → U16) (k : Nat) :
    (mark m 428#usize k).val = if k = 26 then (m k).val ||| 4096 else (m k).val := by
  simpa only [show (428#usize).val = 428 from rfl] using
    PV_B3_MaskSparseBit.mark_value m 428#usize k
#print axioms mark0428
theorem mark0443 (m : Nat → U16) (k : Nat) :
    (mark m 443#usize k).val = if k = 27 then (m k).val ||| 2048 else (m k).val := by
  simpa only [show (443#usize).val = 443 from rfl] using
    PV_B3_MaskSparseBit.mark_value m 443#usize k
#print axioms mark0443
theorem mark0448 (m : Nat → U16) (k : Nat) :
    (mark m 448#usize k).val = if k = 28 then (m k).val ||| 1 else (m k).val := by
  simpa only [show (448#usize).val = 448 from rfl] using
    PV_B3_MaskSparseBit.mark_value m 448#usize k
#print axioms mark0448
theorem mark0459 (m : Nat → U16) (k : Nat) :
    (mark m 459#usize k).val = if k = 28 then (m k).val ||| 2048 else (m k).val := by
  simpa only [show (459#usize).val = 459 from rfl] using
    PV_B3_MaskSparseBit.mark_value m 459#usize k
#print axioms mark0459
theorem mark0460 (m : Nat → U16) (k : Nat) :
    (mark m 460#usize k).val = if k = 28 then (m k).val ||| 4096 else (m k).val := by
  simpa only [show (460#usize).val = 460 from rfl] using
    PV_B3_MaskSparseBit.mark_value m 460#usize k
#print axioms mark0460
theorem mark0464 (m : Nat → U16) (k : Nat) :
    (mark m 464#usize k).val = if k = 29 then (m k).val ||| 1 else (m k).val := by
  simpa only [show (464#usize).val = 464 from rfl] using
    PV_B3_MaskSparseBit.mark_value m 464#usize k
#print axioms mark0464
theorem mark0475 (m : Nat → U16) (k : Nat) :
    (mark m 475#usize k).val = if k = 29 then (m k).val ||| 2048 else (m k).val := by
  simpa only [show (475#usize).val = 475 from rfl] using
    PV_B3_MaskSparseBit.mark_value m 475#usize k
#print axioms mark0475
theorem mark0491 (m : Nat → U16) (k : Nat) :
    (mark m 491#usize k).val = if k = 30 then (m k).val ||| 2048 else (m k).val := by
  simpa only [show (491#usize).val = 491 from rfl] using
    PV_B3_MaskSparseBit.mark_value m 491#usize k
#print axioms mark0491
theorem mark0496 (m : Nat → U16) (k : Nat) :
    (mark m 496#usize k).val = if k = 31 then (m k).val ||| 1 else (m k).val := by
  simpa only [show (496#usize).val = 496 from rfl] using
    PV_B3_MaskSparseBit.mark_value m 496#usize k
#print axioms mark0496
theorem mark0507 (m : Nat → U16) (k : Nat) :
    (mark m 507#usize k).val = if k = 31 then (m k).val ||| 2048 else (m k).val := by
  simpa only [show (507#usize).val = 507 from rfl] using
    PV_B3_MaskSparseBit.mark_value m 507#usize k
#print axioms mark0507
theorem mark0508 (m : Nat → U16) (k : Nat) :
    (mark m 508#usize k).val = if k = 31 then (m k).val ||| 4096 else (m k).val := by
  simpa only [show (508#usize).val = 508 from rfl] using
    PV_B3_MaskSparseBit.mark_value m 508#usize k
#print axioms mark0508
theorem mark0512 (m : Nat → U16) (k : Nat) :
    (mark m 512#usize k).val = if k = 32 then (m k).val ||| 1 else (m k).val := by
  simpa only [show (512#usize).val = 512 from rfl] using
    PV_B3_MaskSparseBit.mark_value m 512#usize k
#print axioms mark0512
theorem mark0523 (m : Nat → U16) (k : Nat) :
    (mark m 523#usize k).val = if k = 32 then (m k).val ||| 2048 else (m k).val := by
  simpa only [show (523#usize).val = 523 from rfl] using
    PV_B3_MaskSparseBit.mark_value m 523#usize k
#print axioms mark0523
theorem mark0528 (m : Nat → U16) (k : Nat) :
    (mark m 528#usize k).val = if k = 33 then (m k).val ||| 1 else (m k).val := by
  simpa only [show (528#usize).val = 528 from rfl] using
    PV_B3_MaskSparseBit.mark_value m 528#usize k
#print axioms mark0528
theorem mark0539 (m : Nat → U16) (k : Nat) :
    (mark m 539#usize k).val = if k = 33 then (m k).val ||| 2048 else (m k).val := by
  simpa only [show (539#usize).val = 539 from rfl] using
    PV_B3_MaskSparseBit.mark_value m 539#usize k
#print axioms mark0539
theorem mark0540 (m : Nat → U16) (k : Nat) :
    (mark m 540#usize k).val = if k = 33 then (m k).val ||| 4096 else (m k).val := by
  simpa only [show (540#usize).val = 540 from rfl] using
    PV_B3_MaskSparseBit.mark_value m 540#usize k
#print axioms mark0540
theorem mark0544 (m : Nat → U16) (k : Nat) :
    (mark m 544#usize k).val = if k = 34 then (m k).val ||| 1 else (m k).val := by
  simpa only [show (544#usize).val = 544 from rfl] using
    PV_B3_MaskSparseBit.mark_value m 544#usize k
#print axioms mark0544
theorem mark0555 (m : Nat → U16) (k : Nat) :
    (mark m 555#usize k).val = if k = 34 then (m k).val ||| 2048 else (m k).val := by
  simpa only [show (555#usize).val = 555 from rfl] using
    PV_B3_MaskSparseBit.mark_value m 555#usize k
#print axioms mark0555
theorem mark0556 (m : Nat → U16) (k : Nat) :
    (mark m 556#usize k).val = if k = 34 then (m k).val ||| 4096 else (m k).val := by
  simpa only [show (556#usize).val = 556 from rfl] using
    PV_B3_MaskSparseBit.mark_value m 556#usize k
#print axioms mark0556
theorem mark0560 (m : Nat → U16) (k : Nat) :
    (mark m 560#usize k).val = if k = 35 then (m k).val ||| 1 else (m k).val := by
  simpa only [show (560#usize).val = 560 from rfl] using
    PV_B3_MaskSparseBit.mark_value m 560#usize k
#print axioms mark0560
theorem mark0571 (m : Nat → U16) (k : Nat) :
    (mark m 571#usize k).val = if k = 35 then (m k).val ||| 2048 else (m k).val := by
  simpa only [show (571#usize).val = 571 from rfl] using
    PV_B3_MaskSparseBit.mark_value m 571#usize k
#print axioms mark0571
theorem mark0572 (m : Nat → U16) (k : Nat) :
    (mark m 572#usize k).val = if k = 35 then (m k).val ||| 4096 else (m k).val := by
  simpa only [show (572#usize).val = 572 from rfl] using
    PV_B3_MaskSparseBit.mark_value m 572#usize k
#print axioms mark0572
theorem mark0576 (m : Nat → U16) (k : Nat) :
    (mark m 576#usize k).val = if k = 36 then (m k).val ||| 1 else (m k).val := by
  simpa only [show (576#usize).val = 576 from rfl] using
    PV_B3_MaskSparseBit.mark_value m 576#usize k
#print axioms mark0576
theorem mark0587 (m : Nat → U16) (k : Nat) :
    (mark m 587#usize k).val = if k = 36 then (m k).val ||| 2048 else (m k).val := by
  simpa only [show (587#usize).val = 587 from rfl] using
    PV_B3_MaskSparseBit.mark_value m 587#usize k
#print axioms mark0587
theorem mark0588 (m : Nat → U16) (k : Nat) :
    (mark m 588#usize k).val = if k = 36 then (m k).val ||| 4096 else (m k).val := by
  simpa only [show (588#usize).val = 588 from rfl] using
    PV_B3_MaskSparseBit.mark_value m 588#usize k
#print axioms mark0588
theorem mark0592 (m : Nat → U16) (k : Nat) :
    (mark m 592#usize k).val = if k = 37 then (m k).val ||| 1 else (m k).val := by
  simpa only [show (592#usize).val = 592 from rfl] using
    PV_B3_MaskSparseBit.mark_value m 592#usize k
#print axioms mark0592
theorem mark0603 (m : Nat → U16) (k : Nat) :
    (mark m 603#usize k).val = if k = 37 then (m k).val ||| 2048 else (m k).val := by
  simpa only [show (603#usize).val = 603 from rfl] using
    PV_B3_MaskSparseBit.mark_value m 603#usize k
#print axioms mark0603
theorem mark0604 (m : Nat → U16) (k : Nat) :
    (mark m 604#usize k).val = if k = 37 then (m k).val ||| 4096 else (m k).val := by
  simpa only [show (604#usize).val = 604 from rfl] using
    PV_B3_MaskSparseBit.mark_value m 604#usize k
#print axioms mark0604
theorem mark0608 (m : Nat → U16) (k : Nat) :
    (mark m 608#usize k).val = if k = 38 then (m k).val ||| 1 else (m k).val := by
  simpa only [show (608#usize).val = 608 from rfl] using
    PV_B3_MaskSparseBit.mark_value m 608#usize k
#print axioms mark0608
theorem mark0619 (m : Nat → U16) (k : Nat) :
    (mark m 619#usize k).val = if k = 38 then (m k).val ||| 2048 else (m k).val := by
  simpa only [show (619#usize).val = 619 from rfl] using
    PV_B3_MaskSparseBit.mark_value m 619#usize k
#print axioms mark0619
theorem mark0620 (m : Nat → U16) (k : Nat) :
    (mark m 620#usize k).val = if k = 38 then (m k).val ||| 4096 else (m k).val := by
  simpa only [show (620#usize).val = 620 from rfl] using
    PV_B3_MaskSparseBit.mark_value m 620#usize k
#print axioms mark0620
theorem mark0624 (m : Nat → U16) (k : Nat) :
    (mark m 624#usize k).val = if k = 39 then (m k).val ||| 1 else (m k).val := by
  simpa only [show (624#usize).val = 624 from rfl] using
    PV_B3_MaskSparseBit.mark_value m 624#usize k
#print axioms mark0624
theorem mark0635 (m : Nat → U16) (k : Nat) :
    (mark m 635#usize k).val = if k = 39 then (m k).val ||| 2048 else (m k).val := by
  simpa only [show (635#usize).val = 635 from rfl] using
    PV_B3_MaskSparseBit.mark_value m 635#usize k
#print axioms mark0635
theorem mark0636 (m : Nat → U16) (k : Nat) :
    (mark m 636#usize k).val = if k = 39 then (m k).val ||| 4096 else (m k).val := by
  simpa only [show (636#usize).val = 636 from rfl] using
    PV_B3_MaskSparseBit.mark_value m 636#usize k
#print axioms mark0636
theorem mark0640 (m : Nat → U16) (k : Nat) :
    (mark m 640#usize k).val = if k = 40 then (m k).val ||| 1 else (m k).val := by
  simpa only [show (640#usize).val = 640 from rfl] using
    PV_B3_MaskSparseBit.mark_value m 640#usize k
#print axioms mark0640
theorem mark0651 (m : Nat → U16) (k : Nat) :
    (mark m 651#usize k).val = if k = 40 then (m k).val ||| 2048 else (m k).val := by
  simpa only [show (651#usize).val = 651 from rfl] using
    PV_B3_MaskSparseBit.mark_value m 651#usize k
#print axioms mark0651
theorem mark0652 (m : Nat → U16) (k : Nat) :
    (mark m 652#usize k).val = if k = 40 then (m k).val ||| 4096 else (m k).val := by
  simpa only [show (652#usize).val = 652 from rfl] using
    PV_B3_MaskSparseBit.mark_value m 652#usize k
#print axioms mark0652
theorem mark0656 (m : Nat → U16) (k : Nat) :
    (mark m 656#usize k).val = if k = 41 then (m k).val ||| 1 else (m k).val := by
  simpa only [show (656#usize).val = 656 from rfl] using
    PV_B3_MaskSparseBit.mark_value m 656#usize k
#print axioms mark0656
theorem mark0667 (m : Nat → U16) (k : Nat) :
    (mark m 667#usize k).val = if k = 41 then (m k).val ||| 2048 else (m k).val := by
  simpa only [show (667#usize).val = 667 from rfl] using
    PV_B3_MaskSparseBit.mark_value m 667#usize k
#print axioms mark0667
theorem mark0668 (m : Nat → U16) (k : Nat) :
    (mark m 668#usize k).val = if k = 41 then (m k).val ||| 4096 else (m k).val := by
  simpa only [show (668#usize).val = 668 from rfl] using
    PV_B3_MaskSparseBit.mark_value m 668#usize k
#print axioms mark0668
theorem mark0672 (m : Nat → U16) (k : Nat) :
    (mark m 672#usize k).val = if k = 42 then (m k).val ||| 1 else (m k).val := by
  simpa only [show (672#usize).val = 672 from rfl] using
    PV_B3_MaskSparseBit.mark_value m 672#usize k
#print axioms mark0672
theorem mark0683 (m : Nat → U16) (k : Nat) :
    (mark m 683#usize k).val = if k = 42 then (m k).val ||| 2048 else (m k).val := by
  simpa only [show (683#usize).val = 683 from rfl] using
    PV_B3_MaskSparseBit.mark_value m 683#usize k
#print axioms mark0683
theorem mark0684 (m : Nat → U16) (k : Nat) :
    (mark m 684#usize k).val = if k = 42 then (m k).val ||| 4096 else (m k).val := by
  simpa only [show (684#usize).val = 684 from rfl] using
    PV_B3_MaskSparseBit.mark_value m 684#usize k
#print axioms mark0684
theorem mark0688 (m : Nat → U16) (k : Nat) :
    (mark m 688#usize k).val = if k = 43 then (m k).val ||| 1 else (m k).val := by
  simpa only [show (688#usize).val = 688 from rfl] using
    PV_B3_MaskSparseBit.mark_value m 688#usize k
#print axioms mark0688
theorem mark0699 (m : Nat → U16) (k : Nat) :
    (mark m 699#usize k).val = if k = 43 then (m k).val ||| 2048 else (m k).val := by
  simpa only [show (699#usize).val = 699 from rfl] using
    PV_B3_MaskSparseBit.mark_value m 699#usize k
#print axioms mark0699
theorem mark0700 (m : Nat → U16) (k : Nat) :
    (mark m 700#usize k).val = if k = 43 then (m k).val ||| 4096 else (m k).val := by
  simpa only [show (700#usize).val = 700 from rfl] using
    PV_B3_MaskSparseBit.mark_value m 700#usize k
#print axioms mark0700
theorem mark0704 (m : Nat → U16) (k : Nat) :
    (mark m 704#usize k).val = if k = 44 then (m k).val ||| 1 else (m k).val := by
  simpa only [show (704#usize).val = 704 from rfl] using
    PV_B3_MaskSparseBit.mark_value m 704#usize k
#print axioms mark0704
theorem mark0715 (m : Nat → U16) (k : Nat) :
    (mark m 715#usize k).val = if k = 44 then (m k).val ||| 2048 else (m k).val := by
  simpa only [show (715#usize).val = 715 from rfl] using
    PV_B3_MaskSparseBit.mark_value m 715#usize k
#print axioms mark0715
theorem mark0716 (m : Nat → U16) (k : Nat) :
    (mark m 716#usize k).val = if k = 44 then (m k).val ||| 4096 else (m k).val := by
  simpa only [show (716#usize).val = 716 from rfl] using
    PV_B3_MaskSparseBit.mark_value m 716#usize k
#print axioms mark0716
theorem mark0720 (m : Nat → U16) (k : Nat) :
    (mark m 720#usize k).val = if k = 45 then (m k).val ||| 1 else (m k).val := by
  simpa only [show (720#usize).val = 720 from rfl] using
    PV_B3_MaskSparseBit.mark_value m 720#usize k
#print axioms mark0720
theorem mark0731 (m : Nat → U16) (k : Nat) :
    (mark m 731#usize k).val = if k = 45 then (m k).val ||| 2048 else (m k).val := by
  simpa only [show (731#usize).val = 731 from rfl] using
    PV_B3_MaskSparseBit.mark_value m 731#usize k
#print axioms mark0731
theorem mark0732 (m : Nat → U16) (k : Nat) :
    (mark m 732#usize k).val = if k = 45 then (m k).val ||| 4096 else (m k).val := by
  simpa only [show (732#usize).val = 732 from rfl] using
    PV_B3_MaskSparseBit.mark_value m 732#usize k
#print axioms mark0732
theorem mark0736 (m : Nat → U16) (k : Nat) :
    (mark m 736#usize k).val = if k = 46 then (m k).val ||| 1 else (m k).val := by
  simpa only [show (736#usize).val = 736 from rfl] using
    PV_B3_MaskSparseBit.mark_value m 736#usize k
#print axioms mark0736
theorem mark0747 (m : Nat → U16) (k : Nat) :
    (mark m 747#usize k).val = if k = 46 then (m k).val ||| 2048 else (m k).val := by
  simpa only [show (747#usize).val = 747 from rfl] using
    PV_B3_MaskSparseBit.mark_value m 747#usize k
#print axioms mark0747
theorem mark0748 (m : Nat → U16) (k : Nat) :
    (mark m 748#usize k).val = if k = 46 then (m k).val ||| 4096 else (m k).val := by
  simpa only [show (748#usize).val = 748 from rfl] using
    PV_B3_MaskSparseBit.mark_value m 748#usize k
#print axioms mark0748
theorem mark0752 (m : Nat → U16) (k : Nat) :
    (mark m 752#usize k).val = if k = 47 then (m k).val ||| 1 else (m k).val := by
  simpa only [show (752#usize).val = 752 from rfl] using
    PV_B3_MaskSparseBit.mark_value m 752#usize k
#print axioms mark0752
theorem mark0763 (m : Nat → U16) (k : Nat) :
    (mark m 763#usize k).val = if k = 47 then (m k).val ||| 2048 else (m k).val := by
  simpa only [show (763#usize).val = 763 from rfl] using
    PV_B3_MaskSparseBit.mark_value m 763#usize k
#print axioms mark0763
theorem mark0764 (m : Nat → U16) (k : Nat) :
    (mark m 764#usize k).val = if k = 47 then (m k).val ||| 4096 else (m k).val := by
  simpa only [show (764#usize).val = 764 from rfl] using
    PV_B3_MaskSparseBit.mark_value m 764#usize k
#print axioms mark0764
theorem mark0768 (m : Nat → U16) (k : Nat) :
    (mark m 768#usize k).val = if k = 48 then (m k).val ||| 1 else (m k).val := by
  simpa only [show (768#usize).val = 768 from rfl] using
    PV_B3_MaskSparseBit.mark_value m 768#usize k
#print axioms mark0768
theorem mark0779 (m : Nat → U16) (k : Nat) :
    (mark m 779#usize k).val = if k = 48 then (m k).val ||| 2048 else (m k).val := by
  simpa only [show (779#usize).val = 779 from rfl] using
    PV_B3_MaskSparseBit.mark_value m 779#usize k
#print axioms mark0779
theorem mark0780 (m : Nat → U16) (k : Nat) :
    (mark m 780#usize k).val = if k = 48 then (m k).val ||| 4096 else (m k).val := by
  simpa only [show (780#usize).val = 780 from rfl] using
    PV_B3_MaskSparseBit.mark_value m 780#usize k
#print axioms mark0780
theorem mark0784 (m : Nat → U16) (k : Nat) :
    (mark m 784#usize k).val = if k = 49 then (m k).val ||| 1 else (m k).val := by
  simpa only [show (784#usize).val = 784 from rfl] using
    PV_B3_MaskSparseBit.mark_value m 784#usize k
#print axioms mark0784
theorem mark0795 (m : Nat → U16) (k : Nat) :
    (mark m 795#usize k).val = if k = 49 then (m k).val ||| 2048 else (m k).val := by
  simpa only [show (795#usize).val = 795 from rfl] using
    PV_B3_MaskSparseBit.mark_value m 795#usize k
#print axioms mark0795
theorem mark0796 (m : Nat → U16) (k : Nat) :
    (mark m 796#usize k).val = if k = 49 then (m k).val ||| 4096 else (m k).val := by
  simpa only [show (796#usize).val = 796 from rfl] using
    PV_B3_MaskSparseBit.mark_value m 796#usize k
#print axioms mark0796
theorem mark0800 (m : Nat → U16) (k : Nat) :
    (mark m 800#usize k).val = if k = 50 then (m k).val ||| 1 else (m k).val := by
  simpa only [show (800#usize).val = 800 from rfl] using
    PV_B3_MaskSparseBit.mark_value m 800#usize k
#print axioms mark0800
theorem mark0811 (m : Nat → U16) (k : Nat) :
    (mark m 811#usize k).val = if k = 50 then (m k).val ||| 2048 else (m k).val := by
  simpa only [show (811#usize).val = 811 from rfl] using
    PV_B3_MaskSparseBit.mark_value m 811#usize k
#print axioms mark0811
theorem mark0812 (m : Nat → U16) (k : Nat) :
    (mark m 812#usize k).val = if k = 50 then (m k).val ||| 4096 else (m k).val := by
  simpa only [show (812#usize).val = 812 from rfl] using
    PV_B3_MaskSparseBit.mark_value m 812#usize k
#print axioms mark0812
theorem mark0816 (m : Nat → U16) (k : Nat) :
    (mark m 816#usize k).val = if k = 51 then (m k).val ||| 1 else (m k).val := by
  simpa only [show (816#usize).val = 816 from rfl] using
    PV_B3_MaskSparseBit.mark_value m 816#usize k
#print axioms mark0816
theorem mark0827 (m : Nat → U16) (k : Nat) :
    (mark m 827#usize k).val = if k = 51 then (m k).val ||| 2048 else (m k).val := by
  simpa only [show (827#usize).val = 827 from rfl] using
    PV_B3_MaskSparseBit.mark_value m 827#usize k
#print axioms mark0827
theorem mark0828 (m : Nat → U16) (k : Nat) :
    (mark m 828#usize k).val = if k = 51 then (m k).val ||| 4096 else (m k).val := by
  simpa only [show (828#usize).val = 828 from rfl] using
    PV_B3_MaskSparseBit.mark_value m 828#usize k
#print axioms mark0828
theorem mark0832 (m : Nat → U16) (k : Nat) :
    (mark m 832#usize k).val = if k = 52 then (m k).val ||| 1 else (m k).val := by
  simpa only [show (832#usize).val = 832 from rfl] using
    PV_B3_MaskSparseBit.mark_value m 832#usize k
#print axioms mark0832
theorem mark0843 (m : Nat → U16) (k : Nat) :
    (mark m 843#usize k).val = if k = 52 then (m k).val ||| 2048 else (m k).val := by
  simpa only [show (843#usize).val = 843 from rfl] using
    PV_B3_MaskSparseBit.mark_value m 843#usize k
#print axioms mark0843
theorem mark0844 (m : Nat → U16) (k : Nat) :
    (mark m 844#usize k).val = if k = 52 then (m k).val ||| 4096 else (m k).val := by
  simpa only [show (844#usize).val = 844 from rfl] using
    PV_B3_MaskSparseBit.mark_value m 844#usize k
#print axioms mark0844
theorem mark0848 (m : Nat → U16) (k : Nat) :
    (mark m 848#usize k).val = if k = 53 then (m k).val ||| 1 else (m k).val := by
  simpa only [show (848#usize).val = 848 from rfl] using
    PV_B3_MaskSparseBit.mark_value m 848#usize k
#print axioms mark0848
theorem mark0860 (m : Nat → U16) (k : Nat) :
    (mark m 860#usize k).val = if k = 53 then (m k).val ||| 4096 else (m k).val := by
  simpa only [show (860#usize).val = 860 from rfl] using
    PV_B3_MaskSparseBit.mark_value m 860#usize k
#print axioms mark0860
theorem mark0864 (m : Nat → U16) (k : Nat) :
    (mark m 864#usize k).val = if k = 54 then (m k).val ||| 1 else (m k).val := by
  simpa only [show (864#usize).val = 864 from rfl] using
    PV_B3_MaskSparseBit.mark_value m 864#usize k
#print axioms mark0864
theorem mark0875 (m : Nat → U16) (k : Nat) :
    (mark m 875#usize k).val = if k = 54 then (m k).val ||| 2048 else (m k).val := by
  simpa only [show (875#usize).val = 875 from rfl] using
    PV_B3_MaskSparseBit.mark_value m 875#usize k
#print axioms mark0875
theorem mark0876 (m : Nat → U16) (k : Nat) :
    (mark m 876#usize k).val = if k = 54 then (m k).val ||| 4096 else (m k).val := by
  simpa only [show (876#usize).val = 876 from rfl] using
    PV_B3_MaskSparseBit.mark_value m 876#usize k
#print axioms mark0876
theorem mark0880 (m : Nat → U16) (k : Nat) :
    (mark m 880#usize k).val = if k = 55 then (m k).val ||| 1 else (m k).val := by
  simpa only [show (880#usize).val = 880 from rfl] using
    PV_B3_MaskSparseBit.mark_value m 880#usize k
#print axioms mark0880
theorem mark0891 (m : Nat → U16) (k : Nat) :
    (mark m 891#usize k).val = if k = 55 then (m k).val ||| 2048 else (m k).val := by
  simpa only [show (891#usize).val = 891 from rfl] using
    PV_B3_MaskSparseBit.mark_value m 891#usize k
#print axioms mark0891
theorem mark0892 (m : Nat → U16) (k : Nat) :
    (mark m 892#usize k).val = if k = 55 then (m k).val ||| 4096 else (m k).val := by
  simpa only [show (892#usize).val = 892 from rfl] using
    PV_B3_MaskSparseBit.mark_value m 892#usize k
#print axioms mark0892
theorem mark0896 (m : Nat → U16) (k : Nat) :
    (mark m 896#usize k).val = if k = 56 then (m k).val ||| 1 else (m k).val := by
  simpa only [show (896#usize).val = 896 from rfl] using
    PV_B3_MaskSparseBit.mark_value m 896#usize k
#print axioms mark0896
theorem mark0908 (m : Nat → U16) (k : Nat) :
    (mark m 908#usize k).val = if k = 56 then (m k).val ||| 4096 else (m k).val := by
  simpa only [show (908#usize).val = 908 from rfl] using
    PV_B3_MaskSparseBit.mark_value m 908#usize k
#print axioms mark0908
theorem mark0913 (m : Nat → U16) (k : Nat) :
    (mark m 913#usize k).val = if k = 57 then (m k).val ||| 2 else (m k).val := by
  simpa only [show (913#usize).val = 913 from rfl] using
    PV_B3_MaskSparseBit.mark_value m 913#usize k
#print axioms mark0913
theorem mark0914 (m : Nat → U16) (k : Nat) :
    (mark m 914#usize k).val = if k = 57 then (m k).val ||| 4 else (m k).val := by
  simpa only [show (914#usize).val = 914 from rfl] using
    PV_B3_MaskSparseBit.mark_value m 914#usize k
#print axioms mark0914
theorem mark0917 (m : Nat → U16) (k : Nat) :
    (mark m 917#usize k).val = if k = 57 then (m k).val ||| 32 else (m k).val := by
  simpa only [show (917#usize).val = 917 from rfl] using
    PV_B3_MaskSparseBit.mark_value m 917#usize k
#print axioms mark0917
theorem mark0918 (m : Nat → U16) (k : Nat) :
    (mark m 918#usize k).val = if k = 57 then (m k).val ||| 64 else (m k).val := by
  simpa only [show (918#usize).val = 918 from rfl] using
    PV_B3_MaskSparseBit.mark_value m 918#usize k
#print axioms mark0918
theorem mark0921 (m : Nat → U16) (k : Nat) :
    (mark m 921#usize k).val = if k = 57 then (m k).val ||| 512 else (m k).val := by
  simpa only [show (921#usize).val = 921 from rfl] using
    PV_B3_MaskSparseBit.mark_value m 921#usize k
#print axioms mark0921
theorem mark0922 (m : Nat → U16) (k : Nat) :
    (mark m 922#usize k).val = if k = 57 then (m k).val ||| 1024 else (m k).val := by
  simpa only [show (922#usize).val = 922 from rfl] using
    PV_B3_MaskSparseBit.mark_value m 922#usize k
#print axioms mark0922
theorem mark0925 (m : Nat → U16) (k : Nat) :
    (mark m 925#usize k).val = if k = 57 then (m k).val ||| 8192 else (m k).val := by
  simpa only [show (925#usize).val = 925 from rfl] using
    PV_B3_MaskSparseBit.mark_value m 925#usize k
#print axioms mark0925
theorem mark0926 (m : Nat → U16) (k : Nat) :
    (mark m 926#usize k).val = if k = 57 then (m k).val ||| 16384 else (m k).val := by
  simpa only [show (926#usize).val = 926 from rfl] using
    PV_B3_MaskSparseBit.mark_value m 926#usize k
#print axioms mark0926
theorem mark0929 (m : Nat → U16) (k : Nat) :
    (mark m 929#usize k).val = if k = 58 then (m k).val ||| 2 else (m k).val := by
  simpa only [show (929#usize).val = 929 from rfl] using
    PV_B3_MaskSparseBit.mark_value m 929#usize k
#print axioms mark0929
theorem mark0930 (m : Nat → U16) (k : Nat) :
    (mark m 930#usize k).val = if k = 58 then (m k).val ||| 4 else (m k).val := by
  simpa only [show (930#usize).val = 930 from rfl] using
    PV_B3_MaskSparseBit.mark_value m 930#usize k
#print axioms mark0930
theorem mark0933 (m : Nat → U16) (k : Nat) :
    (mark m 933#usize k).val = if k = 58 then (m k).val ||| 32 else (m k).val := by
  simpa only [show (933#usize).val = 933 from rfl] using
    PV_B3_MaskSparseBit.mark_value m 933#usize k
#print axioms mark0933
theorem mark0934 (m : Nat → U16) (k : Nat) :
    (mark m 934#usize k).val = if k = 58 then (m k).val ||| 64 else (m k).val := by
  simpa only [show (934#usize).val = 934 from rfl] using
    PV_B3_MaskSparseBit.mark_value m 934#usize k
#print axioms mark0934
theorem mark0937 (m : Nat → U16) (k : Nat) :
    (mark m 937#usize k).val = if k = 58 then (m k).val ||| 512 else (m k).val := by
  simpa only [show (937#usize).val = 937 from rfl] using
    PV_B3_MaskSparseBit.mark_value m 937#usize k
#print axioms mark0937
theorem mark0938 (m : Nat → U16) (k : Nat) :
    (mark m 938#usize k).val = if k = 58 then (m k).val ||| 1024 else (m k).val := by
  simpa only [show (938#usize).val = 938 from rfl] using
    PV_B3_MaskSparseBit.mark_value m 938#usize k
#print axioms mark0938
theorem mark0941 (m : Nat → U16) (k : Nat) :
    (mark m 941#usize k).val = if k = 58 then (m k).val ||| 8192 else (m k).val := by
  simpa only [show (941#usize).val = 941 from rfl] using
    PV_B3_MaskSparseBit.mark_value m 941#usize k
#print axioms mark0941
theorem mark0942 (m : Nat → U16) (k : Nat) :
    (mark m 942#usize k).val = if k = 58 then (m k).val ||| 16384 else (m k).val := by
  simpa only [show (942#usize).val = 942 from rfl] using
    PV_B3_MaskSparseBit.mark_value m 942#usize k
#print axioms mark0942
theorem mark0945 (m : Nat → U16) (k : Nat) :
    (mark m 945#usize k).val = if k = 59 then (m k).val ||| 2 else (m k).val := by
  simpa only [show (945#usize).val = 945 from rfl] using
    PV_B3_MaskSparseBit.mark_value m 945#usize k
#print axioms mark0945
theorem mark0946 (m : Nat → U16) (k : Nat) :
    (mark m 946#usize k).val = if k = 59 then (m k).val ||| 4 else (m k).val := by
  simpa only [show (946#usize).val = 946 from rfl] using
    PV_B3_MaskSparseBit.mark_value m 946#usize k
#print axioms mark0946
theorem mark0949 (m : Nat → U16) (k : Nat) :
    (mark m 949#usize k).val = if k = 59 then (m k).val ||| 32 else (m k).val := by
  simpa only [show (949#usize).val = 949 from rfl] using
    PV_B3_MaskSparseBit.mark_value m 949#usize k
#print axioms mark0949
theorem mark0950 (m : Nat → U16) (k : Nat) :
    (mark m 950#usize k).val = if k = 59 then (m k).val ||| 64 else (m k).val := by
  simpa only [show (950#usize).val = 950 from rfl] using
    PV_B3_MaskSparseBit.mark_value m 950#usize k
#print axioms mark0950
theorem mark0953 (m : Nat → U16) (k : Nat) :
    (mark m 953#usize k).val = if k = 59 then (m k).val ||| 512 else (m k).val := by
  simpa only [show (953#usize).val = 953 from rfl] using
    PV_B3_MaskSparseBit.mark_value m 953#usize k
#print axioms mark0953
theorem mark0954 (m : Nat → U16) (k : Nat) :
    (mark m 954#usize k).val = if k = 59 then (m k).val ||| 1024 else (m k).val := by
  simpa only [show (954#usize).val = 954 from rfl] using
    PV_B3_MaskSparseBit.mark_value m 954#usize k
#print axioms mark0954
theorem mark0957 (m : Nat → U16) (k : Nat) :
    (mark m 957#usize k).val = if k = 59 then (m k).val ||| 8192 else (m k).val := by
  simpa only [show (957#usize).val = 957 from rfl] using
    PV_B3_MaskSparseBit.mark_value m 957#usize k
#print axioms mark0957
theorem mark0958 (m : Nat → U16) (k : Nat) :
    (mark m 958#usize k).val = if k = 59 then (m k).val ||| 16384 else (m k).val := by
  simpa only [show (958#usize).val = 958 from rfl] using
    PV_B3_MaskSparseBit.mark_value m 958#usize k
#print axioms mark0958
theorem mark0961 (m : Nat → U16) (k : Nat) :
    (mark m 961#usize k).val = if k = 60 then (m k).val ||| 2 else (m k).val := by
  simpa only [show (961#usize).val = 961 from rfl] using
    PV_B3_MaskSparseBit.mark_value m 961#usize k
#print axioms mark0961
theorem mark0962 (m : Nat → U16) (k : Nat) :
    (mark m 962#usize k).val = if k = 60 then (m k).val ||| 4 else (m k).val := by
  simpa only [show (962#usize).val = 962 from rfl] using
    PV_B3_MaskSparseBit.mark_value m 962#usize k
#print axioms mark0962
theorem mark0965 (m : Nat → U16) (k : Nat) :
    (mark m 965#usize k).val = if k = 60 then (m k).val ||| 32 else (m k).val := by
  simpa only [show (965#usize).val = 965 from rfl] using
    PV_B3_MaskSparseBit.mark_value m 965#usize k
#print axioms mark0965
theorem mark0966 (m : Nat → U16) (k : Nat) :
    (mark m 966#usize k).val = if k = 60 then (m k).val ||| 64 else (m k).val := by
  simpa only [show (966#usize).val = 966 from rfl] using
    PV_B3_MaskSparseBit.mark_value m 966#usize k
#print axioms mark0966
theorem mark0969 (m : Nat → U16) (k : Nat) :
    (mark m 969#usize k).val = if k = 60 then (m k).val ||| 512 else (m k).val := by
  simpa only [show (969#usize).val = 969 from rfl] using
    PV_B3_MaskSparseBit.mark_value m 969#usize k
#print axioms mark0969
theorem mark0970 (m : Nat → U16) (k : Nat) :
    (mark m 970#usize k).val = if k = 60 then (m k).val ||| 1024 else (m k).val := by
  simpa only [show (970#usize).val = 970 from rfl] using
    PV_B3_MaskSparseBit.mark_value m 970#usize k
#print axioms mark0970
theorem mark0973 (m : Nat → U16) (k : Nat) :
    (mark m 973#usize k).val = if k = 60 then (m k).val ||| 8192 else (m k).val := by
  simpa only [show (973#usize).val = 973 from rfl] using
    PV_B3_MaskSparseBit.mark_value m 973#usize k
#print axioms mark0973
theorem mark0974 (m : Nat → U16) (k : Nat) :
    (mark m 974#usize k).val = if k = 60 then (m k).val ||| 16384 else (m k).val := by
  simpa only [show (974#usize).val = 974 from rfl] using
    PV_B3_MaskSparseBit.mark_value m 974#usize k
#print axioms mark0974
theorem mark0977 (m : Nat → U16) (k : Nat) :
    (mark m 977#usize k).val = if k = 61 then (m k).val ||| 2 else (m k).val := by
  simpa only [show (977#usize).val = 977 from rfl] using
    PV_B3_MaskSparseBit.mark_value m 977#usize k
#print axioms mark0977
theorem mark0978 (m : Nat → U16) (k : Nat) :
    (mark m 978#usize k).val = if k = 61 then (m k).val ||| 4 else (m k).val := by
  simpa only [show (978#usize).val = 978 from rfl] using
    PV_B3_MaskSparseBit.mark_value m 978#usize k
#print axioms mark0978
theorem mark0981 (m : Nat → U16) (k : Nat) :
    (mark m 981#usize k).val = if k = 61 then (m k).val ||| 32 else (m k).val := by
  simpa only [show (981#usize).val = 981 from rfl] using
    PV_B3_MaskSparseBit.mark_value m 981#usize k
#print axioms mark0981
theorem mark0982 (m : Nat → U16) (k : Nat) :
    (mark m 982#usize k).val = if k = 61 then (m k).val ||| 64 else (m k).val := by
  simpa only [show (982#usize).val = 982 from rfl] using
    PV_B3_MaskSparseBit.mark_value m 982#usize k
#print axioms mark0982
theorem mark0985 (m : Nat → U16) (k : Nat) :
    (mark m 985#usize k).val = if k = 61 then (m k).val ||| 512 else (m k).val := by
  simpa only [show (985#usize).val = 985 from rfl] using
    PV_B3_MaskSparseBit.mark_value m 985#usize k
#print axioms mark0985
theorem mark0986 (m : Nat → U16) (k : Nat) :
    (mark m 986#usize k).val = if k = 61 then (m k).val ||| 1024 else (m k).val := by
  simpa only [show (986#usize).val = 986 from rfl] using
    PV_B3_MaskSparseBit.mark_value m 986#usize k
#print axioms mark0986
theorem mark0989 (m : Nat → U16) (k : Nat) :
    (mark m 989#usize k).val = if k = 61 then (m k).val ||| 8192 else (m k).val := by
  simpa only [show (989#usize).val = 989 from rfl] using
    PV_B3_MaskSparseBit.mark_value m 989#usize k
#print axioms mark0989
theorem mark0990 (m : Nat → U16) (k : Nat) :
    (mark m 990#usize k).val = if k = 61 then (m k).val ||| 16384 else (m k).val := by
  simpa only [show (990#usize).val = 990 from rfl] using
    PV_B3_MaskSparseBit.mark_value m 990#usize k
#print axioms mark0990
theorem mark0993 (m : Nat → U16) (k : Nat) :
    (mark m 993#usize k).val = if k = 62 then (m k).val ||| 2 else (m k).val := by
  simpa only [show (993#usize).val = 993 from rfl] using
    PV_B3_MaskSparseBit.mark_value m 993#usize k
#print axioms mark0993
theorem mark0994 (m : Nat → U16) (k : Nat) :
    (mark m 994#usize k).val = if k = 62 then (m k).val ||| 4 else (m k).val := by
  simpa only [show (994#usize).val = 994 from rfl] using
    PV_B3_MaskSparseBit.mark_value m 994#usize k
#print axioms mark0994
theorem mark0997 (m : Nat → U16) (k : Nat) :
    (mark m 997#usize k).val = if k = 62 then (m k).val ||| 32 else (m k).val := by
  simpa only [show (997#usize).val = 997 from rfl] using
    PV_B3_MaskSparseBit.mark_value m 997#usize k
#print axioms mark0997
theorem mark0998 (m : Nat → U16) (k : Nat) :
    (mark m 998#usize k).val = if k = 62 then (m k).val ||| 64 else (m k).val := by
  simpa only [show (998#usize).val = 998 from rfl] using
    PV_B3_MaskSparseBit.mark_value m 998#usize k
#print axioms mark0998
theorem mark1001 (m : Nat → U16) (k : Nat) :
    (mark m 1001#usize k).val = if k = 62 then (m k).val ||| 512 else (m k).val := by
  simpa only [show (1001#usize).val = 1001 from rfl] using
    PV_B3_MaskSparseBit.mark_value m 1001#usize k
#print axioms mark1001
theorem mark1002 (m : Nat → U16) (k : Nat) :
    (mark m 1002#usize k).val = if k = 62 then (m k).val ||| 1024 else (m k).val := by
  simpa only [show (1002#usize).val = 1002 from rfl] using
    PV_B3_MaskSparseBit.mark_value m 1002#usize k
#print axioms mark1002
theorem mark1005 (m : Nat → U16) (k : Nat) :
    (mark m 1005#usize k).val = if k = 62 then (m k).val ||| 8192 else (m k).val := by
  simpa only [show (1005#usize).val = 1005 from rfl] using
    PV_B3_MaskSparseBit.mark_value m 1005#usize k
#print axioms mark1005
theorem mark1006 (m : Nat → U16) (k : Nat) :
    (mark m 1006#usize k).val = if k = 62 then (m k).val ||| 16384 else (m k).val := by
  simpa only [show (1006#usize).val = 1006 from rfl] using
    PV_B3_MaskSparseBit.mark_value m 1006#usize k
#print axioms mark1006
theorem mark1008 (m : Nat → U16) (k : Nat) :
    (mark m 1008#usize k).val = if k = 63 then (m k).val ||| 1 else (m k).val := by
  simpa only [show (1008#usize).val = 1008 from rfl] using
    PV_B3_MaskSparseBit.mark_value m 1008#usize k
#print axioms mark1008
theorem mark1010 (m : Nat → U16) (k : Nat) :
    (mark m 1010#usize k).val = if k = 63 then (m k).val ||| 4 else (m k).val := by
  simpa only [show (1010#usize).val = 1010 from rfl] using
    PV_B3_MaskSparseBit.mark_value m 1010#usize k
#print axioms mark1010
theorem mark1012 (m : Nat → U16) (k : Nat) :
    (mark m 1012#usize k).val = if k = 63 then (m k).val ||| 16 else (m k).val := by
  simpa only [show (1012#usize).val = 1012 from rfl] using
    PV_B3_MaskSparseBit.mark_value m 1012#usize k
#print axioms mark1012
theorem mark1014 (m : Nat → U16) (k : Nat) :
    (mark m 1014#usize k).val = if k = 63 then (m k).val ||| 64 else (m k).val := by
  simpa only [show (1014#usize).val = 1014 from rfl] using
    PV_B3_MaskSparseBit.mark_value m 1014#usize k
#print axioms mark1014
theorem mark1015 (m : Nat → U16) (k : Nat) :
    (mark m 1015#usize k).val = if k = 63 then (m k).val ||| 128 else (m k).val := by
  simpa only [show (1015#usize).val = 1015 from rfl] using
    PV_B3_MaskSparseBit.mark_value m 1015#usize k
#print axioms mark1015
theorem mark1017 (m : Nat → U16) (k : Nat) :
    (mark m 1017#usize k).val = if k = 63 then (m k).val ||| 512 else (m k).val := by
  simpa only [show (1017#usize).val = 1017 from rfl] using
    PV_B3_MaskSparseBit.mark_value m 1017#usize k
#print axioms mark1017
theorem mark1018 (m : Nat → U16) (k : Nat) :
    (mark m 1018#usize k).val = if k = 63 then (m k).val ||| 1024 else (m k).val := by
  simpa only [show (1018#usize).val = 1018 from rfl] using
    PV_B3_MaskSparseBit.mark_value m 1018#usize k
#print axioms mark1018
end PV_B3_MaskSparseMarks
