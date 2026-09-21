import AspisV8R17.RawReducerNat

/-! Pure modular-word interface shared by runtime execution and tower algebra.
No generated-runtime declarations or cryptographic premises are imported. -/
namespace AspisV8R17.GeneratedQM31Products
open RawReducer
abbrev WordPair := Nat × Nat
def addWords (x y : WordPair) : WordPair := ((x.1+y.1)%P,(x.2+y.2)%P)
def subWords (x y : WordPair) : WordPair := ((x.1+P-y.1)%P,(x.2+P-y.2)%P)
def mulWords (x y : WordPair) : WordPair :=
  (((x.1*y.1)%P+P-(x.2*y.2)%P)%P,
   ((((x.1+x.2)*(y.1+y.2))%P+P-(x.1*y.1)%P)%P+P-(x.2*y.2)%P)%P)
def rWords (x : WordPair) : WordPair :=
  (((x.1+x.1)%P+P-x.2)%P,(x.1+(x.2+x.2)%P)%P)
def qmMulWords (x y : WordPair × WordPair) :=
  let m0 := mulWords x.1 y.1
  let m1 := mulWords x.2 y.2
  (addWords m0 (rWords m1),
   subWords (subWords (mulWords (addWords x.1 x.2) (addWords y.1 y.2)) m0) m1)
def qmSquareWords (x : WordPair × WordPair) :=
  (addWords (mulWords x.1 x.1) (rWords (mulWords x.2 x.2)),
   addWords (mulWords x.1 x.2) (mulWords x.1 x.2))
end AspisV8R17.GeneratedQM31Products

namespace AspisV8R17.GeneratedQM31Linear
open GeneratedQM31Products
def qmAddWords (x y : WordPair × WordPair) :=
  (addWords x.1 y.1, addWords x.2 y.2)
def qmSubWords (x y : WordPair × WordPair) :=
  (subWords x.1 y.1, subWords x.2 y.2)
end AspisV8R17.GeneratedQM31Linear
