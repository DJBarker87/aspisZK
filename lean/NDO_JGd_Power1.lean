import NDO_JGd_Power0
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGd_Power1
open JGd_ExactWords
attribute [local irreducible] HPow.hPow HMul.hMul HAdd.hAdd
def x16 : W := ((1905225606,1674966669),(36767123,1820461701))
theorem product16 : value ((1097185556,956973529),(1330160683,1876022401)) * value ((1097185556,956973529),(1330160683,1876022401)) = value x16 := by
  apply mul
  change AspisV8R17.GeneratedQM31Products.qmMulWords ((1097185556,956973529),(1330160683,1876022401)) ((1097185556,956973529),(1330160683,1876022401)) = ((1905225606,1674966669),(36767123,1820461701))
  norm_num [AspisV8R17.GeneratedQM31Products.qmMulWords, AspisV8R17.GeneratedQM31Linear.qmAddWords, AspisV8R17.GeneratedQM31Products.addWords, AspisV8R17.GeneratedQM31Products.subWords, AspisV8R17.GeneratedQM31Products.mulWords, AspisV8R17.GeneratedQM31Products.rWords, AspisV8R17.RawReducer.P]
#print axioms product16
theorem power16 : value JGd_Linear00.sum16 ^ 16 = value x16 := by
  calc
    _ = value JGd_Linear00.sum16 ^ 8 * value JGd_Linear00.sum16 ^ 8 := pow_add _ 8 8
    _ = value ((1097185556,956973529),(1330160683,1876022401)) * value ((1097185556,956973529),(1330160683,1876022401)) := by rw [JGd_Power0.power8]; rfl
    _ = value x16 := product16
#print axioms power16
def x24 : W := ((1108354341,285940904),(482630007,1392143490))
theorem product24 : value ((1905225606,1674966669),(36767123,1820461701)) * value ((1097185556,956973529),(1330160683,1876022401)) = value x24 := by
  apply mul
  change AspisV8R17.GeneratedQM31Products.qmMulWords ((1905225606,1674966669),(36767123,1820461701)) ((1097185556,956973529),(1330160683,1876022401)) = ((1108354341,285940904),(482630007,1392143490))
  norm_num [AspisV8R17.GeneratedQM31Products.qmMulWords, AspisV8R17.GeneratedQM31Linear.qmAddWords, AspisV8R17.GeneratedQM31Products.addWords, AspisV8R17.GeneratedQM31Products.subWords, AspisV8R17.GeneratedQM31Products.mulWords, AspisV8R17.GeneratedQM31Products.rWords, AspisV8R17.RawReducer.P]
#print axioms product24
theorem power24 : value JGd_Linear00.sum16 ^ 24 = value x24 := by
  calc
    _ = value JGd_Linear00.sum16 ^ 16 * value JGd_Linear00.sum16 ^ 8 := pow_add _ 16 8
    _ = value ((1905225606,1674966669),(36767123,1820461701)) * value ((1097185556,956973529),(1330160683,1876022401)) := by rw [JGd_Power0.power8,power16]; rfl
    _ = value x24 := product24
#print axioms power24
def x26 : W := ((60053924,1891194216),(2090430923,260852809))
theorem product26 : value ((1108354341,285940904),(482630007,1392143490)) * value ((1531476310,1969303434),(1758728985,882344282)) = value x26 := by
  apply mul
  change AspisV8R17.GeneratedQM31Products.qmMulWords ((1108354341,285940904),(482630007,1392143490)) ((1531476310,1969303434),(1758728985,882344282)) = ((60053924,1891194216),(2090430923,260852809))
  norm_num [AspisV8R17.GeneratedQM31Products.qmMulWords, AspisV8R17.GeneratedQM31Linear.qmAddWords, AspisV8R17.GeneratedQM31Products.addWords, AspisV8R17.GeneratedQM31Products.subWords, AspisV8R17.GeneratedQM31Products.mulWords, AspisV8R17.GeneratedQM31Products.rWords, AspisV8R17.RawReducer.P]
#print axioms product26
theorem power26 : value JGd_Linear00.sum16 ^ 26 = value x26 := by
  calc
    _ = value JGd_Linear00.sum16 ^ 24 * value JGd_Linear00.sum16 ^ 2 := pow_add _ 24 2
    _ = value ((1108354341,285940904),(482630007,1392143490)) * value ((1531476310,1969303434),(1758728985,882344282)) := by rw [JGd_Power0.power2,power24]; rfl
    _ = value x26 := product26
#print axioms power26
end AspisR1.JGd_Power1
end
