import NDO_JHl_WeightBytes00
import NDO_JHl_WeightBytes01
import NDO_JHl_WeightBytes02
import NDO_JHl_WeightBytes03
import NDO_JHl_WeightBytes04
import NDO_JHl_WeightBytes05
import NDO_JHl_WeightBytes06
import NDO_JHl_WeightBytes07
import NDO_JHl_WeightBytes08
import NDO_JHl_WeightBytes09
import NDO_JHl_WeightBytes10
import NDO_JHl_WeightBytes11
import NDO_JHl_WeightBytes12
import NDO_JHl_WeightBytes13
import NDO_JHl_WeightBytes14
import NDO_JHl_WeightBytes15
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHl_AllWeightCells

theorem source (j : Fin 64) : JHl_WeightCell.Law j := by
  fin_cases j
  · exact JHl_WeightBytes00.cell00
  · exact JHl_WeightBytes00.cell01
  · exact JHl_WeightBytes00.cell02
  · exact JHl_WeightBytes00.cell03
  · exact JHl_WeightBytes01.cell04
  · exact JHl_WeightBytes01.cell05
  · exact JHl_WeightBytes01.cell06
  · exact JHl_WeightBytes01.cell07
  · exact JHl_WeightBytes02.cell08
  · exact JHl_WeightBytes02.cell09
  · exact JHl_WeightBytes02.cell10
  · exact JHl_WeightBytes02.cell11
  · exact JHl_WeightBytes03.cell12
  · exact JHl_WeightBytes03.cell13
  · exact JHl_WeightBytes03.cell14
  · exact JHl_WeightBytes03.cell15
  · exact JHl_WeightBytes04.cell16
  · exact JHl_WeightBytes04.cell17
  · exact JHl_WeightBytes04.cell18
  · exact JHl_WeightBytes04.cell19
  · exact JHl_WeightBytes05.cell20
  · exact JHl_WeightBytes05.cell21
  · exact JHl_WeightBytes05.cell22
  · exact JHl_WeightBytes05.cell23
  · exact JHl_WeightBytes06.cell24
  · exact JHl_WeightBytes06.cell25
  · exact JHl_WeightBytes06.cell26
  · exact JHl_WeightBytes06.cell27
  · exact JHl_WeightBytes07.cell28
  · exact JHl_WeightBytes07.cell29
  · exact JHl_WeightBytes07.cell30
  · exact JHl_WeightBytes07.cell31
  · exact JHl_WeightBytes08.cell32
  · exact JHl_WeightBytes08.cell33
  · exact JHl_WeightBytes08.cell34
  · exact JHl_WeightBytes08.cell35
  · exact JHl_WeightBytes09.cell36
  · exact JHl_WeightBytes09.cell37
  · exact JHl_WeightBytes09.cell38
  · exact JHl_WeightBytes09.cell39
  · exact JHl_WeightBytes10.cell40
  · exact JHl_WeightBytes10.cell41
  · exact JHl_WeightBytes10.cell42
  · exact JHl_WeightBytes10.cell43
  · exact JHl_WeightBytes11.cell44
  · exact JHl_WeightBytes11.cell45
  · exact JHl_WeightBytes11.cell46
  · exact JHl_WeightBytes11.cell47
  · exact JHl_WeightBytes12.cell48
  · exact JHl_WeightBytes12.cell49
  · exact JHl_WeightBytes12.cell50
  · exact JHl_WeightBytes12.cell51
  · exact JHl_WeightBytes13.cell52
  · exact JHl_WeightBytes13.cell53
  · exact JHl_WeightBytes13.cell54
  · exact JHl_WeightBytes13.cell55
  · exact JHl_WeightBytes14.cell56
  · exact JHl_WeightBytes14.cell57
  · exact JHl_WeightBytes14.cell58
  · exact JHl_WeightBytes14.cell59
  · exact JHl_WeightBytes15.cell60
  · exact JHl_WeightBytes15.cell61
  · exact JHl_WeightBytes15.cell62
  · exact JHl_WeightBytes15.cell63
#print axioms source
end AspisR1.JHl_AllWeightCells
end
