import NDO_JGd_LinearValue
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGd_Power0
open JGd_ExactWords
attribute [local irreducible] HPow.hPow HMul.hMul HAdd.hAdd
def x2 : W := ((1531476310,1969303434),(1758728985,882344282))
theorem product2 : value ((533099968,803914706),(1501807103,1266007432)) * value ((533099968,803914706),(1501807103,1266007432)) = value x2 := by
  apply mul
  change AspisV8R17.GeneratedQM31Products.qmMulWords ((533099968,803914706),(1501807103,1266007432)) ((533099968,803914706),(1501807103,1266007432)) = ((1531476310,1969303434),(1758728985,882344282))
  norm_num [AspisV8R17.GeneratedQM31Products.qmMulWords, AspisV8R17.GeneratedQM31Linear.qmAddWords, AspisV8R17.GeneratedQM31Products.addWords, AspisV8R17.GeneratedQM31Products.subWords, AspisV8R17.GeneratedQM31Products.mulWords, AspisV8R17.GeneratedQM31Products.rWords, AspisV8R17.RawReducer.P]
#print axioms product2
theorem power2 : value JGd_Linear00.sum16 ^ 2 = value x2 := by
  calc
    _ = value JGd_Linear00.sum16 ^ 1 * value JGd_Linear00.sum16 ^ 1 := pow_add _ 1 1
    _ = value ((533099968,803914706),(1501807103,1266007432)) * value ((533099968,803914706),(1501807103,1266007432)) := by rw [pow_one]; rfl
    _ = value x2 := product2
#print axioms power2
def x4 : W := ((1560725912,1926284706),(43999510,244424117))
theorem product4 : value ((1531476310,1969303434),(1758728985,882344282)) * value ((1531476310,1969303434),(1758728985,882344282)) = value x4 := by
  apply mul
  change AspisV8R17.GeneratedQM31Products.qmMulWords ((1531476310,1969303434),(1758728985,882344282)) ((1531476310,1969303434),(1758728985,882344282)) = ((1560725912,1926284706),(43999510,244424117))
  norm_num [AspisV8R17.GeneratedQM31Products.qmMulWords, AspisV8R17.GeneratedQM31Linear.qmAddWords, AspisV8R17.GeneratedQM31Products.addWords, AspisV8R17.GeneratedQM31Products.subWords, AspisV8R17.GeneratedQM31Products.mulWords, AspisV8R17.GeneratedQM31Products.rWords, AspisV8R17.RawReducer.P]
#print axioms product4
theorem power4 : value JGd_Linear00.sum16 ^ 4 = value x4 := by
  calc
    _ = value JGd_Linear00.sum16 ^ 2 * value JGd_Linear00.sum16 ^ 2 := pow_add _ 2 2
    _ = value ((1531476310,1969303434),(1758728985,882344282)) * value ((1531476310,1969303434),(1758728985,882344282)) := by rw [JGd_Power0.power2]; rfl
    _ = value x4 := product4
#print axioms power4
def x8 : W := ((1097185556,956973529),(1330160683,1876022401))
theorem product8 : value ((1560725912,1926284706),(43999510,244424117)) * value ((1560725912,1926284706),(43999510,244424117)) = value x8 := by
  apply mul
  change AspisV8R17.GeneratedQM31Products.qmMulWords ((1560725912,1926284706),(43999510,244424117)) ((1560725912,1926284706),(43999510,244424117)) = ((1097185556,956973529),(1330160683,1876022401))
  norm_num [AspisV8R17.GeneratedQM31Products.qmMulWords, AspisV8R17.GeneratedQM31Linear.qmAddWords, AspisV8R17.GeneratedQM31Products.addWords, AspisV8R17.GeneratedQM31Products.subWords, AspisV8R17.GeneratedQM31Products.mulWords, AspisV8R17.GeneratedQM31Products.rWords, AspisV8R17.RawReducer.P]
#print axioms product8
theorem power8 : value JGd_Linear00.sum16 ^ 8 = value x8 := by
  calc
    _ = value JGd_Linear00.sum16 ^ 4 * value JGd_Linear00.sum16 ^ 4 := pow_add _ 4 4
    _ = value ((1560725912,1926284706),(43999510,244424117)) * value ((1560725912,1926284706),(43999510,244424117)) := by rw [JGd_Power0.power4]; rfl
    _ = value x8 := product8
#print axioms power8
end AspisR1.JGd_Power0
end
