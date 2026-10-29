import R1Z.PV_RDB2E_FallbackArray4
import R1Z.PV_RDB2E_FallbackBlock

section
-- Unchanged source component R1Z.PV_CBL_FallbackConstants
open Aeneas Aeneas.Std Result
namespace R1Z.PV_CBL_FallbackConstants
set_option autoImplicit false
def words : List U32 := [
  1116352408#u32, 1899447441#u32, 3049323471#u32, 3921009573#u32,
  961987163#u32, 1508970993#u32, 2453635748#u32, 2870763221#u32,
  3624381080#u32, 310598401#u32, 607225278#u32, 1426881987#u32,
  1925078388#u32, 2162078206#u32, 2614888103#u32, 3248222580#u32,
  3835390401#u32, 4022224774#u32, 264347078#u32, 604807628#u32,
  770255983#u32, 1249150122#u32, 1555081692#u32, 1996064986#u32,
  2554220882#u32, 2821834349#u32, 2952996808#u32, 3210313671#u32,
  3336571891#u32, 3584528711#u32, 113926993#u32, 338241895#u32,
  666307205#u32, 773529912#u32, 1294757372#u32, 1396182291#u32,
  1695183700#u32, 1986661051#u32, 2177026350#u32, 2456956037#u32,
  2730485921#u32, 2820302411#u32, 3259730800#u32, 3345764771#u32,
  3516065817#u32, 3600352804#u32, 4094571909#u32, 275423344#u32,
  430227734#u32, 506948616#u32, 659060556#u32, 883997877#u32,
  958139571#u32, 1322822218#u32, 1537002063#u32, 1747873779#u32,
  1955562222#u32, 2024104815#u32, 2227730452#u32, 2361852424#u32,
  2428436474#u32, 2756734187#u32, 3204031479#u32, 3329325298#u32
]
theorem words_length : words.length=64 := rfl
#print axioms words
#print axioms words_length
end R1Z.PV_CBL_FallbackConstants

end

section
-- Unchanged source component R1Z.PV_CBL_FallbackConstantMatrix
open Aeneas Aeneas.Std Result
namespace R1Z.PV_CBL_FallbackConstantMatrix
set_option autoImplicit false
def q0 : Array U32 4#usize := PV_CBL_FallbackArray4.pack 3921009573#u32 3049323471#u32 1899447441#u32 1116352408#u32
def q1 : Array U32 4#usize := PV_CBL_FallbackArray4.pack 2870763221#u32 2453635748#u32 1508970993#u32 961987163#u32
def q2 : Array U32 4#usize := PV_CBL_FallbackArray4.pack 1426881987#u32 607225278#u32 310598401#u32 3624381080#u32
def q3 : Array U32 4#usize := PV_CBL_FallbackArray4.pack 3248222580#u32 2614888103#u32 2162078206#u32 1925078388#u32
def q4 : Array U32 4#usize := PV_CBL_FallbackArray4.pack 604807628#u32 264347078#u32 4022224774#u32 3835390401#u32
def q5 : Array U32 4#usize := PV_CBL_FallbackArray4.pack 1996064986#u32 1555081692#u32 1249150122#u32 770255983#u32
def q6 : Array U32 4#usize := PV_CBL_FallbackArray4.pack 3210313671#u32 2952996808#u32 2821834349#u32 2554220882#u32
def q7 : Array U32 4#usize := PV_CBL_FallbackArray4.pack 338241895#u32 113926993#u32 3584528711#u32 3336571891#u32
def q8 : Array U32 4#usize := PV_CBL_FallbackArray4.pack 1396182291#u32 1294757372#u32 773529912#u32 666307205#u32
def q9 : Array U32 4#usize := PV_CBL_FallbackArray4.pack 2456956037#u32 2177026350#u32 1986661051#u32 1695183700#u32
def q10 : Array U32 4#usize := PV_CBL_FallbackArray4.pack 3345764771#u32 3259730800#u32 2820302411#u32 2730485921#u32
def q11 : Array U32 4#usize := PV_CBL_FallbackArray4.pack 275423344#u32 4094571909#u32 3600352804#u32 3516065817#u32
def q12 : Array U32 4#usize := PV_CBL_FallbackArray4.pack 883997877#u32 659060556#u32 506948616#u32 430227734#u32
def q13 : Array U32 4#usize := PV_CBL_FallbackArray4.pack 1747873779#u32 1537002063#u32 1322822218#u32 958139571#u32
def q14 : Array U32 4#usize := PV_CBL_FallbackArray4.pack 2361852424#u32 2227730452#u32 2024104815#u32 1955562222#u32
def q15 : Array U32 4#usize := PV_CBL_FallbackArray4.pack 3329325298#u32 3204031479#u32 2756734187#u32 2428436474#u32
def matrix : Array (Array U32 4#usize) 16#usize := ⟨[q0,q1,q2,q3,q4,q5,q6,q7,q8,q9,q10,q11,q12,q13,q14,q15],by simp⟩
theorem words_source : PV_CBL_FallbackBlock.sha_fallback_consts.K32.val=PV_CBL_FallbackConstants.words := by
  unfold PV_CBL_FallbackBlock.sha_fallback_consts.K32
  rfl
#print axioms q0
#print axioms q1
#print axioms q2
#print axioms q3
#print axioms q4
#print axioms q5
#print axioms q6
#print axioms q7
#print axioms q8
#print axioms q9
#print axioms q10
#print axioms q11
#print axioms q12
#print axioms q13
#print axioms q14
#print axioms q15
#print axioms matrix
#print axioms words_source
end R1Z.PV_CBL_FallbackConstantMatrix

end

section
-- Unchanged source component R1Z.PV_CBL_FallbackConstant00
open Aeneas Aeneas.Std Result
namespace R1Z.PV_CBL_FallbackConstant00
set_option autoImplicit false
theorem word0 : Array.index_usize PV_CBL_FallbackBlock.sha_fallback_consts.K32 0#usize = ok 1116352408#u32 := by
  unfold PV_CBL_FallbackBlock.sha_fallback_consts.K32
  rfl
theorem word1 : Array.index_usize PV_CBL_FallbackBlock.sha_fallback_consts.K32 1#usize = ok 1899447441#u32 := by
  unfold PV_CBL_FallbackBlock.sha_fallback_consts.K32
  rfl
theorem word2 : Array.index_usize PV_CBL_FallbackBlock.sha_fallback_consts.K32 2#usize = ok 3049323471#u32 := by
  unfold PV_CBL_FallbackBlock.sha_fallback_consts.K32
  rfl
theorem word3 : Array.index_usize PV_CBL_FallbackBlock.sha_fallback_consts.K32 3#usize = ok 3921009573#u32 := by
  unfold PV_CBL_FallbackBlock.sha_fallback_consts.K32
  rfl
theorem vector : Array.index_usize PV_CBL_FallbackConstantMatrix.matrix 0#usize =
    ok PV_CBL_FallbackConstantMatrix.q0 := by
  rfl
#print axioms word0
#print axioms word1
#print axioms word2
#print axioms word3
#print axioms vector
end R1Z.PV_CBL_FallbackConstant00

end

section
-- Unchanged source component R1Z.PV_CBL_FallbackConstant01
open Aeneas Aeneas.Std Result
namespace R1Z.PV_CBL_FallbackConstant01
set_option autoImplicit false
theorem word0 : Array.index_usize PV_CBL_FallbackBlock.sha_fallback_consts.K32 4#usize = ok 961987163#u32 := by
  unfold PV_CBL_FallbackBlock.sha_fallback_consts.K32
  rfl
theorem word1 : Array.index_usize PV_CBL_FallbackBlock.sha_fallback_consts.K32 5#usize = ok 1508970993#u32 := by
  unfold PV_CBL_FallbackBlock.sha_fallback_consts.K32
  rfl
theorem word2 : Array.index_usize PV_CBL_FallbackBlock.sha_fallback_consts.K32 6#usize = ok 2453635748#u32 := by
  unfold PV_CBL_FallbackBlock.sha_fallback_consts.K32
  rfl
theorem word3 : Array.index_usize PV_CBL_FallbackBlock.sha_fallback_consts.K32 7#usize = ok 2870763221#u32 := by
  unfold PV_CBL_FallbackBlock.sha_fallback_consts.K32
  rfl
theorem vector : Array.index_usize PV_CBL_FallbackConstantMatrix.matrix 1#usize =
    ok PV_CBL_FallbackConstantMatrix.q1 := by
  rfl
#print axioms word0
#print axioms word1
#print axioms word2
#print axioms word3
#print axioms vector
end R1Z.PV_CBL_FallbackConstant01

end

section
-- Unchanged source component R1Z.PV_CBL_FallbackConstant02
open Aeneas Aeneas.Std Result
namespace R1Z.PV_CBL_FallbackConstant02
set_option autoImplicit false
theorem word0 : Array.index_usize PV_CBL_FallbackBlock.sha_fallback_consts.K32 8#usize = ok 3624381080#u32 := by
  unfold PV_CBL_FallbackBlock.sha_fallback_consts.K32
  rfl
theorem word1 : Array.index_usize PV_CBL_FallbackBlock.sha_fallback_consts.K32 9#usize = ok 310598401#u32 := by
  unfold PV_CBL_FallbackBlock.sha_fallback_consts.K32
  rfl
theorem word2 : Array.index_usize PV_CBL_FallbackBlock.sha_fallback_consts.K32 10#usize = ok 607225278#u32 := by
  unfold PV_CBL_FallbackBlock.sha_fallback_consts.K32
  rfl
theorem word3 : Array.index_usize PV_CBL_FallbackBlock.sha_fallback_consts.K32 11#usize = ok 1426881987#u32 := by
  unfold PV_CBL_FallbackBlock.sha_fallback_consts.K32
  rfl
theorem vector : Array.index_usize PV_CBL_FallbackConstantMatrix.matrix 2#usize =
    ok PV_CBL_FallbackConstantMatrix.q2 := by
  rfl
#print axioms word0
#print axioms word1
#print axioms word2
#print axioms word3
#print axioms vector
end R1Z.PV_CBL_FallbackConstant02

end

section
-- Unchanged source component R1Z.PV_CBL_FallbackConstant03
open Aeneas Aeneas.Std Result
namespace R1Z.PV_CBL_FallbackConstant03
set_option autoImplicit false
theorem word0 : Array.index_usize PV_CBL_FallbackBlock.sha_fallback_consts.K32 12#usize = ok 1925078388#u32 := by
  unfold PV_CBL_FallbackBlock.sha_fallback_consts.K32
  rfl
theorem word1 : Array.index_usize PV_CBL_FallbackBlock.sha_fallback_consts.K32 13#usize = ok 2162078206#u32 := by
  unfold PV_CBL_FallbackBlock.sha_fallback_consts.K32
  rfl
theorem word2 : Array.index_usize PV_CBL_FallbackBlock.sha_fallback_consts.K32 14#usize = ok 2614888103#u32 := by
  unfold PV_CBL_FallbackBlock.sha_fallback_consts.K32
  rfl
theorem word3 : Array.index_usize PV_CBL_FallbackBlock.sha_fallback_consts.K32 15#usize = ok 3248222580#u32 := by
  unfold PV_CBL_FallbackBlock.sha_fallback_consts.K32
  rfl
theorem vector : Array.index_usize PV_CBL_FallbackConstantMatrix.matrix 3#usize =
    ok PV_CBL_FallbackConstantMatrix.q3 := by
  rfl
#print axioms word0
#print axioms word1
#print axioms word2
#print axioms word3
#print axioms vector
end R1Z.PV_CBL_FallbackConstant03

end

section
-- Unchanged source component R1Z.PV_CBL_FallbackConstant04
open Aeneas Aeneas.Std Result
namespace R1Z.PV_CBL_FallbackConstant04
set_option autoImplicit false
theorem word0 : Array.index_usize PV_CBL_FallbackBlock.sha_fallback_consts.K32 16#usize = ok 3835390401#u32 := by
  unfold PV_CBL_FallbackBlock.sha_fallback_consts.K32
  rfl
theorem word1 : Array.index_usize PV_CBL_FallbackBlock.sha_fallback_consts.K32 17#usize = ok 4022224774#u32 := by
  unfold PV_CBL_FallbackBlock.sha_fallback_consts.K32
  rfl
theorem word2 : Array.index_usize PV_CBL_FallbackBlock.sha_fallback_consts.K32 18#usize = ok 264347078#u32 := by
  unfold PV_CBL_FallbackBlock.sha_fallback_consts.K32
  rfl
theorem word3 : Array.index_usize PV_CBL_FallbackBlock.sha_fallback_consts.K32 19#usize = ok 604807628#u32 := by
  unfold PV_CBL_FallbackBlock.sha_fallback_consts.K32
  rfl
theorem vector : Array.index_usize PV_CBL_FallbackConstantMatrix.matrix 4#usize =
    ok PV_CBL_FallbackConstantMatrix.q4 := by
  rfl
#print axioms word0
#print axioms word1
#print axioms word2
#print axioms word3
#print axioms vector
end R1Z.PV_CBL_FallbackConstant04

end

section
-- Unchanged source component R1Z.PV_CBL_FallbackConstant05
open Aeneas Aeneas.Std Result
namespace R1Z.PV_CBL_FallbackConstant05
set_option autoImplicit false
theorem word0 : Array.index_usize PV_CBL_FallbackBlock.sha_fallback_consts.K32 20#usize = ok 770255983#u32 := by
  unfold PV_CBL_FallbackBlock.sha_fallback_consts.K32
  rfl
theorem word1 : Array.index_usize PV_CBL_FallbackBlock.sha_fallback_consts.K32 21#usize = ok 1249150122#u32 := by
  unfold PV_CBL_FallbackBlock.sha_fallback_consts.K32
  rfl
theorem word2 : Array.index_usize PV_CBL_FallbackBlock.sha_fallback_consts.K32 22#usize = ok 1555081692#u32 := by
  unfold PV_CBL_FallbackBlock.sha_fallback_consts.K32
  rfl
theorem word3 : Array.index_usize PV_CBL_FallbackBlock.sha_fallback_consts.K32 23#usize = ok 1996064986#u32 := by
  unfold PV_CBL_FallbackBlock.sha_fallback_consts.K32
  rfl
theorem vector : Array.index_usize PV_CBL_FallbackConstantMatrix.matrix 5#usize =
    ok PV_CBL_FallbackConstantMatrix.q5 := by
  rfl
#print axioms word0
#print axioms word1
#print axioms word2
#print axioms word3
#print axioms vector
end R1Z.PV_CBL_FallbackConstant05

end

section
-- Unchanged source component R1Z.PV_CBL_FallbackConstant06
open Aeneas Aeneas.Std Result
namespace R1Z.PV_CBL_FallbackConstant06
set_option autoImplicit false
theorem word0 : Array.index_usize PV_CBL_FallbackBlock.sha_fallback_consts.K32 24#usize = ok 2554220882#u32 := by
  unfold PV_CBL_FallbackBlock.sha_fallback_consts.K32
  rfl
theorem word1 : Array.index_usize PV_CBL_FallbackBlock.sha_fallback_consts.K32 25#usize = ok 2821834349#u32 := by
  unfold PV_CBL_FallbackBlock.sha_fallback_consts.K32
  rfl
theorem word2 : Array.index_usize PV_CBL_FallbackBlock.sha_fallback_consts.K32 26#usize = ok 2952996808#u32 := by
  unfold PV_CBL_FallbackBlock.sha_fallback_consts.K32
  rfl
theorem word3 : Array.index_usize PV_CBL_FallbackBlock.sha_fallback_consts.K32 27#usize = ok 3210313671#u32 := by
  unfold PV_CBL_FallbackBlock.sha_fallback_consts.K32
  rfl
theorem vector : Array.index_usize PV_CBL_FallbackConstantMatrix.matrix 6#usize =
    ok PV_CBL_FallbackConstantMatrix.q6 := by
  rfl
#print axioms word0
#print axioms word1
#print axioms word2
#print axioms word3
#print axioms vector
end R1Z.PV_CBL_FallbackConstant06

end

section
-- Unchanged source component R1Z.PV_CBL_FallbackConstant07
open Aeneas Aeneas.Std Result
namespace R1Z.PV_CBL_FallbackConstant07
set_option autoImplicit false
theorem word0 : Array.index_usize PV_CBL_FallbackBlock.sha_fallback_consts.K32 28#usize = ok 3336571891#u32 := by
  unfold PV_CBL_FallbackBlock.sha_fallback_consts.K32
  rfl
theorem word1 : Array.index_usize PV_CBL_FallbackBlock.sha_fallback_consts.K32 29#usize = ok 3584528711#u32 := by
  unfold PV_CBL_FallbackBlock.sha_fallback_consts.K32
  rfl
theorem word2 : Array.index_usize PV_CBL_FallbackBlock.sha_fallback_consts.K32 30#usize = ok 113926993#u32 := by
  unfold PV_CBL_FallbackBlock.sha_fallback_consts.K32
  rfl
theorem word3 : Array.index_usize PV_CBL_FallbackBlock.sha_fallback_consts.K32 31#usize = ok 338241895#u32 := by
  unfold PV_CBL_FallbackBlock.sha_fallback_consts.K32
  rfl
theorem vector : Array.index_usize PV_CBL_FallbackConstantMatrix.matrix 7#usize =
    ok PV_CBL_FallbackConstantMatrix.q7 := by
  rfl
#print axioms word0
#print axioms word1
#print axioms word2
#print axioms word3
#print axioms vector
end R1Z.PV_CBL_FallbackConstant07

end

section
-- Unchanged source component R1Z.PV_CBL_FallbackConstant08
open Aeneas Aeneas.Std Result
namespace R1Z.PV_CBL_FallbackConstant08
set_option autoImplicit false
theorem word0 : Array.index_usize PV_CBL_FallbackBlock.sha_fallback_consts.K32 32#usize = ok 666307205#u32 := by
  unfold PV_CBL_FallbackBlock.sha_fallback_consts.K32
  rfl
theorem word1 : Array.index_usize PV_CBL_FallbackBlock.sha_fallback_consts.K32 33#usize = ok 773529912#u32 := by
  unfold PV_CBL_FallbackBlock.sha_fallback_consts.K32
  rfl
theorem word2 : Array.index_usize PV_CBL_FallbackBlock.sha_fallback_consts.K32 34#usize = ok 1294757372#u32 := by
  unfold PV_CBL_FallbackBlock.sha_fallback_consts.K32
  rfl
theorem word3 : Array.index_usize PV_CBL_FallbackBlock.sha_fallback_consts.K32 35#usize = ok 1396182291#u32 := by
  unfold PV_CBL_FallbackBlock.sha_fallback_consts.K32
  rfl
theorem vector : Array.index_usize PV_CBL_FallbackConstantMatrix.matrix 8#usize =
    ok PV_CBL_FallbackConstantMatrix.q8 := by
  rfl
#print axioms word0
#print axioms word1
#print axioms word2
#print axioms word3
#print axioms vector
end R1Z.PV_CBL_FallbackConstant08

end

section
-- Unchanged source component R1Z.PV_CBL_FallbackConstant09
open Aeneas Aeneas.Std Result
namespace R1Z.PV_CBL_FallbackConstant09
set_option autoImplicit false
theorem word0 : Array.index_usize PV_CBL_FallbackBlock.sha_fallback_consts.K32 36#usize = ok 1695183700#u32 := by
  unfold PV_CBL_FallbackBlock.sha_fallback_consts.K32
  rfl
theorem word1 : Array.index_usize PV_CBL_FallbackBlock.sha_fallback_consts.K32 37#usize = ok 1986661051#u32 := by
  unfold PV_CBL_FallbackBlock.sha_fallback_consts.K32
  rfl
theorem word2 : Array.index_usize PV_CBL_FallbackBlock.sha_fallback_consts.K32 38#usize = ok 2177026350#u32 := by
  unfold PV_CBL_FallbackBlock.sha_fallback_consts.K32
  rfl
theorem word3 : Array.index_usize PV_CBL_FallbackBlock.sha_fallback_consts.K32 39#usize = ok 2456956037#u32 := by
  unfold PV_CBL_FallbackBlock.sha_fallback_consts.K32
  rfl
theorem vector : Array.index_usize PV_CBL_FallbackConstantMatrix.matrix 9#usize =
    ok PV_CBL_FallbackConstantMatrix.q9 := by
  rfl
#print axioms word0
#print axioms word1
#print axioms word2
#print axioms word3
#print axioms vector
end R1Z.PV_CBL_FallbackConstant09

end

section
-- Unchanged source component R1Z.PV_CBL_FallbackConstant10
open Aeneas Aeneas.Std Result
namespace R1Z.PV_CBL_FallbackConstant10
set_option autoImplicit false
theorem word0 : Array.index_usize PV_CBL_FallbackBlock.sha_fallback_consts.K32 40#usize = ok 2730485921#u32 := by
  unfold PV_CBL_FallbackBlock.sha_fallback_consts.K32
  rfl
theorem word1 : Array.index_usize PV_CBL_FallbackBlock.sha_fallback_consts.K32 41#usize = ok 2820302411#u32 := by
  unfold PV_CBL_FallbackBlock.sha_fallback_consts.K32
  rfl
theorem word2 : Array.index_usize PV_CBL_FallbackBlock.sha_fallback_consts.K32 42#usize = ok 3259730800#u32 := by
  unfold PV_CBL_FallbackBlock.sha_fallback_consts.K32
  rfl
theorem word3 : Array.index_usize PV_CBL_FallbackBlock.sha_fallback_consts.K32 43#usize = ok 3345764771#u32 := by
  unfold PV_CBL_FallbackBlock.sha_fallback_consts.K32
  rfl
theorem vector : Array.index_usize PV_CBL_FallbackConstantMatrix.matrix 10#usize =
    ok PV_CBL_FallbackConstantMatrix.q10 := by
  rfl
#print axioms word0
#print axioms word1
#print axioms word2
#print axioms word3
#print axioms vector
end R1Z.PV_CBL_FallbackConstant10

end

section
-- Unchanged source component R1Z.PV_CBL_FallbackConstant11
open Aeneas Aeneas.Std Result
namespace R1Z.PV_CBL_FallbackConstant11
set_option autoImplicit false
theorem word0 : Array.index_usize PV_CBL_FallbackBlock.sha_fallback_consts.K32 44#usize = ok 3516065817#u32 := by
  unfold PV_CBL_FallbackBlock.sha_fallback_consts.K32
  rfl
theorem word1 : Array.index_usize PV_CBL_FallbackBlock.sha_fallback_consts.K32 45#usize = ok 3600352804#u32 := by
  unfold PV_CBL_FallbackBlock.sha_fallback_consts.K32
  rfl
theorem word2 : Array.index_usize PV_CBL_FallbackBlock.sha_fallback_consts.K32 46#usize = ok 4094571909#u32 := by
  unfold PV_CBL_FallbackBlock.sha_fallback_consts.K32
  rfl
theorem word3 : Array.index_usize PV_CBL_FallbackBlock.sha_fallback_consts.K32 47#usize = ok 275423344#u32 := by
  unfold PV_CBL_FallbackBlock.sha_fallback_consts.K32
  rfl
theorem vector : Array.index_usize PV_CBL_FallbackConstantMatrix.matrix 11#usize =
    ok PV_CBL_FallbackConstantMatrix.q11 := by
  rfl
#print axioms word0
#print axioms word1
#print axioms word2
#print axioms word3
#print axioms vector
end R1Z.PV_CBL_FallbackConstant11

end

section
-- Unchanged source component R1Z.PV_CBL_FallbackConstant12
open Aeneas Aeneas.Std Result
namespace R1Z.PV_CBL_FallbackConstant12
set_option autoImplicit false
theorem word0 : Array.index_usize PV_CBL_FallbackBlock.sha_fallback_consts.K32 48#usize = ok 430227734#u32 := by
  unfold PV_CBL_FallbackBlock.sha_fallback_consts.K32
  rfl
theorem word1 : Array.index_usize PV_CBL_FallbackBlock.sha_fallback_consts.K32 49#usize = ok 506948616#u32 := by
  unfold PV_CBL_FallbackBlock.sha_fallback_consts.K32
  rfl
theorem word2 : Array.index_usize PV_CBL_FallbackBlock.sha_fallback_consts.K32 50#usize = ok 659060556#u32 := by
  unfold PV_CBL_FallbackBlock.sha_fallback_consts.K32
  rfl
theorem word3 : Array.index_usize PV_CBL_FallbackBlock.sha_fallback_consts.K32 51#usize = ok 883997877#u32 := by
  unfold PV_CBL_FallbackBlock.sha_fallback_consts.K32
  rfl
theorem vector : Array.index_usize PV_CBL_FallbackConstantMatrix.matrix 12#usize =
    ok PV_CBL_FallbackConstantMatrix.q12 := by
  rfl
#print axioms word0
#print axioms word1
#print axioms word2
#print axioms word3
#print axioms vector
end R1Z.PV_CBL_FallbackConstant12

end

section
-- Unchanged source component R1Z.PV_CBL_FallbackConstant13
open Aeneas Aeneas.Std Result
namespace R1Z.PV_CBL_FallbackConstant13
set_option autoImplicit false
theorem word0 : Array.index_usize PV_CBL_FallbackBlock.sha_fallback_consts.K32 52#usize = ok 958139571#u32 := by
  unfold PV_CBL_FallbackBlock.sha_fallback_consts.K32
  rfl
theorem word1 : Array.index_usize PV_CBL_FallbackBlock.sha_fallback_consts.K32 53#usize = ok 1322822218#u32 := by
  unfold PV_CBL_FallbackBlock.sha_fallback_consts.K32
  rfl
theorem word2 : Array.index_usize PV_CBL_FallbackBlock.sha_fallback_consts.K32 54#usize = ok 1537002063#u32 := by
  unfold PV_CBL_FallbackBlock.sha_fallback_consts.K32
  rfl
theorem word3 : Array.index_usize PV_CBL_FallbackBlock.sha_fallback_consts.K32 55#usize = ok 1747873779#u32 := by
  unfold PV_CBL_FallbackBlock.sha_fallback_consts.K32
  rfl
theorem vector : Array.index_usize PV_CBL_FallbackConstantMatrix.matrix 13#usize =
    ok PV_CBL_FallbackConstantMatrix.q13 := by
  rfl
#print axioms word0
#print axioms word1
#print axioms word2
#print axioms word3
#print axioms vector
end R1Z.PV_CBL_FallbackConstant13

end

section
-- Unchanged source component R1Z.PV_CBL_FallbackConstant14
open Aeneas Aeneas.Std Result
namespace R1Z.PV_CBL_FallbackConstant14
set_option autoImplicit false
theorem word0 : Array.index_usize PV_CBL_FallbackBlock.sha_fallback_consts.K32 56#usize = ok 1955562222#u32 := by
  unfold PV_CBL_FallbackBlock.sha_fallback_consts.K32
  rfl
theorem word1 : Array.index_usize PV_CBL_FallbackBlock.sha_fallback_consts.K32 57#usize = ok 2024104815#u32 := by
  unfold PV_CBL_FallbackBlock.sha_fallback_consts.K32
  rfl
theorem word2 : Array.index_usize PV_CBL_FallbackBlock.sha_fallback_consts.K32 58#usize = ok 2227730452#u32 := by
  unfold PV_CBL_FallbackBlock.sha_fallback_consts.K32
  rfl
theorem word3 : Array.index_usize PV_CBL_FallbackBlock.sha_fallback_consts.K32 59#usize = ok 2361852424#u32 := by
  unfold PV_CBL_FallbackBlock.sha_fallback_consts.K32
  rfl
theorem vector : Array.index_usize PV_CBL_FallbackConstantMatrix.matrix 14#usize =
    ok PV_CBL_FallbackConstantMatrix.q14 := by
  rfl
#print axioms word0
#print axioms word1
#print axioms word2
#print axioms word3
#print axioms vector
end R1Z.PV_CBL_FallbackConstant14

end

section
-- Unchanged source component R1Z.PV_CBL_FallbackConstant15
open Aeneas Aeneas.Std Result
namespace R1Z.PV_CBL_FallbackConstant15
set_option autoImplicit false
theorem word0 : Array.index_usize PV_CBL_FallbackBlock.sha_fallback_consts.K32 60#usize = ok 2428436474#u32 := by
  unfold PV_CBL_FallbackBlock.sha_fallback_consts.K32
  rfl
theorem word1 : Array.index_usize PV_CBL_FallbackBlock.sha_fallback_consts.K32 61#usize = ok 2756734187#u32 := by
  unfold PV_CBL_FallbackBlock.sha_fallback_consts.K32
  rfl
theorem word2 : Array.index_usize PV_CBL_FallbackBlock.sha_fallback_consts.K32 62#usize = ok 3204031479#u32 := by
  unfold PV_CBL_FallbackBlock.sha_fallback_consts.K32
  rfl
theorem word3 : Array.index_usize PV_CBL_FallbackBlock.sha_fallback_consts.K32 63#usize = ok 3329325298#u32 := by
  unfold PV_CBL_FallbackBlock.sha_fallback_consts.K32
  rfl
theorem vector : Array.index_usize PV_CBL_FallbackConstantMatrix.matrix 15#usize =
    ok PV_CBL_FallbackConstantMatrix.q15 := by
  rfl
#print axioms word0
#print axioms word1
#print axioms word2
#print axioms word3
#print axioms vector
end R1Z.PV_CBL_FallbackConstant15

end

section
-- Unchanged source component R1Z.PV_CBL_FallbackConstantSource
open Aeneas Aeneas.Std Result
namespace R1Z.PV_CBL_FallbackConstantSource
set_option autoImplicit false
theorem source : PV_CBL_FallbackBlock.sha_fallback_consts.K32X4 =
    ok PV_CBL_FallbackConstantMatrix.matrix := by
  simp only [PV_CBL_FallbackBlock.sha_fallback_consts.K32X4,
    PV_CBL_FallbackConstant00.word0, PV_CBL_FallbackConstant00.word1, PV_CBL_FallbackConstant00.word2, PV_CBL_FallbackConstant00.word3,
    PV_CBL_FallbackConstant01.word0, PV_CBL_FallbackConstant01.word1, PV_CBL_FallbackConstant01.word2, PV_CBL_FallbackConstant01.word3,
    PV_CBL_FallbackConstant02.word0, PV_CBL_FallbackConstant02.word1, PV_CBL_FallbackConstant02.word2, PV_CBL_FallbackConstant02.word3,
    PV_CBL_FallbackConstant03.word0, PV_CBL_FallbackConstant03.word1, PV_CBL_FallbackConstant03.word2, PV_CBL_FallbackConstant03.word3,
    PV_CBL_FallbackConstant04.word0, PV_CBL_FallbackConstant04.word1, PV_CBL_FallbackConstant04.word2, PV_CBL_FallbackConstant04.word3,
    PV_CBL_FallbackConstant05.word0, PV_CBL_FallbackConstant05.word1, PV_CBL_FallbackConstant05.word2, PV_CBL_FallbackConstant05.word3,
    PV_CBL_FallbackConstant06.word0, PV_CBL_FallbackConstant06.word1, PV_CBL_FallbackConstant06.word2, PV_CBL_FallbackConstant06.word3,
    PV_CBL_FallbackConstant07.word0, PV_CBL_FallbackConstant07.word1, PV_CBL_FallbackConstant07.word2, PV_CBL_FallbackConstant07.word3,
    PV_CBL_FallbackConstant08.word0, PV_CBL_FallbackConstant08.word1, PV_CBL_FallbackConstant08.word2, PV_CBL_FallbackConstant08.word3,
    PV_CBL_FallbackConstant09.word0, PV_CBL_FallbackConstant09.word1, PV_CBL_FallbackConstant09.word2, PV_CBL_FallbackConstant09.word3,
    PV_CBL_FallbackConstant10.word0, PV_CBL_FallbackConstant10.word1, PV_CBL_FallbackConstant10.word2, PV_CBL_FallbackConstant10.word3,
    PV_CBL_FallbackConstant11.word0, PV_CBL_FallbackConstant11.word1, PV_CBL_FallbackConstant11.word2, PV_CBL_FallbackConstant11.word3,
    PV_CBL_FallbackConstant12.word0, PV_CBL_FallbackConstant12.word1, PV_CBL_FallbackConstant12.word2, PV_CBL_FallbackConstant12.word3,
    PV_CBL_FallbackConstant13.word0, PV_CBL_FallbackConstant13.word1, PV_CBL_FallbackConstant13.word2, PV_CBL_FallbackConstant13.word3,
    PV_CBL_FallbackConstant14.word0, PV_CBL_FallbackConstant14.word1, PV_CBL_FallbackConstant14.word2, PV_CBL_FallbackConstant14.word3,
    PV_CBL_FallbackConstant15.word0, PV_CBL_FallbackConstant15.word1, PV_CBL_FallbackConstant15.word2, PV_CBL_FallbackConstant15.word3,
    bind_tc_ok] <;> rfl
#print axioms source
end R1Z.PV_CBL_FallbackConstantSource

end
