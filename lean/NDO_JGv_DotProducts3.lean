import NDO_JGv_DotData
import SAQ_MixedSource
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGv_DotProducts3
open Aeneas Aeneas.Std Result
open JGv_DotData
def product48 : E := ⟨⟨⟨731533505#u32,2095187866#u32⟩,⟨1413313618#u32,604969099#u32⟩⟩,⟨⟨14711607#u32,1867947714#u32⟩,⟨1031583454#u32,1466629500#u32⟩⟩⟩
theorem mul48 : SAQ_MixedSource.mulE (field ⟨48,by decide⟩) (JGv_WeightsData.cell ⟨48,by decide⟩)=ok product48 := by with_unfolding_all rfl
#print axioms mul48
theorem add48 : FIn_Primitives.add v48 product48=ok v49 := by with_unfolding_all rfl
#print axioms add48
theorem step48 : CheckpointBytes5Output.ofE (state 49)=
    CheckpointBytes5Output.ofE (state 48)+term ⟨48,by decide⟩ := by
  have product := SAQ_MixedSource.mulE_exact _ _ _ JGo_TX2_Message48.canonical48
    (JGv_WeightsData.canonical ⟨48,by decide⟩) mul48
  exact (FIn_Primitives.add_value _ _ _ add48).trans (congrArg (fun t=>CheckpointBytes5Output.ofE v48+t) product.1)
#print axioms step48
def product49 : E := ⟨⟨⟨445804261#u32,1959346967#u32⟩,⟨1672256976#u32,1226647064#u32⟩⟩,⟨⟨1124734901#u32,920576327#u32⟩,⟨1162584039#u32,372110798#u32⟩⟩⟩
theorem mul49 : SAQ_MixedSource.mulE (field ⟨49,by decide⟩) (JGv_WeightsData.cell ⟨49,by decide⟩)=ok product49 := by with_unfolding_all rfl
#print axioms mul49
theorem add49 : FIn_Primitives.add v49 product49=ok v50 := by with_unfolding_all rfl
#print axioms add49
theorem step49 : CheckpointBytes5Output.ofE (state 50)=
    CheckpointBytes5Output.ofE (state 49)+term ⟨49,by decide⟩ := by
  have product := SAQ_MixedSource.mulE_exact _ _ _ JGo_TX2_Message48.canonical49
    (JGv_WeightsData.canonical ⟨49,by decide⟩) mul49
  exact (FIn_Primitives.add_value _ _ _ add49).trans (congrArg (fun t=>CheckpointBytes5Output.ofE v49+t) product.1)
#print axioms step49
def product50 : E := ⟨⟨⟨561524294#u32,1824247689#u32⟩,⟨1627965757#u32,1193800521#u32⟩⟩,⟨⟨384324975#u32,612360535#u32⟩,⟨1006686614#u32,952253741#u32⟩⟩⟩
theorem mul50 : SAQ_MixedSource.mulE (field ⟨50,by decide⟩) (JGv_WeightsData.cell ⟨50,by decide⟩)=ok product50 := by with_unfolding_all rfl
#print axioms mul50
theorem add50 : FIn_Primitives.add v50 product50=ok v51 := by with_unfolding_all rfl
#print axioms add50
theorem step50 : CheckpointBytes5Output.ofE (state 51)=
    CheckpointBytes5Output.ofE (state 50)+term ⟨50,by decide⟩ := by
  have product := SAQ_MixedSource.mulE_exact _ _ _ JGo_TX2_Message48.canonical50
    (JGv_WeightsData.canonical ⟨50,by decide⟩) mul50
  exact (FIn_Primitives.add_value _ _ _ add50).trans (congrArg (fun t=>CheckpointBytes5Output.ofE v50+t) product.1)
#print axioms step50
def product51 : E := ⟨⟨⟨435487738#u32,598021730#u32⟩,⟨616093482#u32,177671798#u32⟩⟩,⟨⟨1539951544#u32,1881020951#u32⟩,⟨1813164611#u32,42600376#u32⟩⟩⟩
theorem mul51 : SAQ_MixedSource.mulE (field ⟨51,by decide⟩) (JGv_WeightsData.cell ⟨51,by decide⟩)=ok product51 := by with_unfolding_all rfl
#print axioms mul51
theorem add51 : FIn_Primitives.add v51 product51=ok v52 := by with_unfolding_all rfl
#print axioms add51
theorem step51 : CheckpointBytes5Output.ofE (state 52)=
    CheckpointBytes5Output.ofE (state 51)+term ⟨51,by decide⟩ := by
  have product := SAQ_MixedSource.mulE_exact _ _ _ JGo_TX2_Message48.canonical51
    (JGv_WeightsData.canonical ⟨51,by decide⟩) mul51
  exact (FIn_Primitives.add_value _ _ _ add51).trans (congrArg (fun t=>CheckpointBytes5Output.ofE v51+t) product.1)
#print axioms step51
def product52 : E := ⟨⟨⟨1689761734#u32,1054855406#u32⟩,⟨675155498#u32,1565985033#u32⟩⟩,⟨⟨1489643620#u32,1807830815#u32⟩,⟨671698939#u32,538693692#u32⟩⟩⟩
theorem mul52 : SAQ_MixedSource.mulE (field ⟨52,by decide⟩) (JGv_WeightsData.cell ⟨52,by decide⟩)=ok product52 := by with_unfolding_all rfl
#print axioms mul52
theorem add52 : FIn_Primitives.add v52 product52=ok v53 := by with_unfolding_all rfl
#print axioms add52
theorem step52 : CheckpointBytes5Output.ofE (state 53)=
    CheckpointBytes5Output.ofE (state 52)+term ⟨52,by decide⟩ := by
  have product := SAQ_MixedSource.mulE_exact _ _ _ JGo_TX2_Message48.canonical52
    (JGv_WeightsData.canonical ⟨52,by decide⟩) mul52
  exact (FIn_Primitives.add_value _ _ _ add52).trans (congrArg (fun t=>CheckpointBytes5Output.ofE v52+t) product.1)
#print axioms step52
def product53 : E := ⟨⟨⟨892908101#u32,1474064737#u32⟩,⟨1943208360#u32,53102312#u32⟩⟩,⟨⟨1716433489#u32,1243975150#u32⟩,⟨1449072546#u32,2041266036#u32⟩⟩⟩
theorem mul53 : SAQ_MixedSource.mulE (field ⟨53,by decide⟩) (JGv_WeightsData.cell ⟨53,by decide⟩)=ok product53 := by with_unfolding_all rfl
#print axioms mul53
theorem add53 : FIn_Primitives.add v53 product53=ok v54 := by with_unfolding_all rfl
#print axioms add53
theorem step53 : CheckpointBytes5Output.ofE (state 54)=
    CheckpointBytes5Output.ofE (state 53)+term ⟨53,by decide⟩ := by
  have product := SAQ_MixedSource.mulE_exact _ _ _ JGo_TX2_Message48.canonical53
    (JGv_WeightsData.canonical ⟨53,by decide⟩) mul53
  exact (FIn_Primitives.add_value _ _ _ add53).trans (congrArg (fun t=>CheckpointBytes5Output.ofE v53+t) product.1)
#print axioms step53
def product54 : E := ⟨⟨⟨497366453#u32,2118420360#u32⟩,⟨1166110764#u32,1918721232#u32⟩⟩,⟨⟨201432841#u32,1656294097#u32⟩,⟨1236680684#u32,739147856#u32⟩⟩⟩
theorem mul54 : SAQ_MixedSource.mulE (field ⟨54,by decide⟩) (JGv_WeightsData.cell ⟨54,by decide⟩)=ok product54 := by with_unfolding_all rfl
#print axioms mul54
theorem add54 : FIn_Primitives.add v54 product54=ok v55 := by with_unfolding_all rfl
#print axioms add54
theorem step54 : CheckpointBytes5Output.ofE (state 55)=
    CheckpointBytes5Output.ofE (state 54)+term ⟨54,by decide⟩ := by
  have product := SAQ_MixedSource.mulE_exact _ _ _ JGo_TX2_Message48.canonical54
    (JGv_WeightsData.canonical ⟨54,by decide⟩) mul54
  exact (FIn_Primitives.add_value _ _ _ add54).trans (congrArg (fun t=>CheckpointBytes5Output.ofE v54+t) product.1)
#print axioms step54
def product55 : E := ⟨⟨⟨842397956#u32,217648297#u32⟩,⟨2141407115#u32,1623433939#u32⟩⟩,⟨⟨165831980#u32,797297221#u32⟩,⟨1633991436#u32,1057330195#u32⟩⟩⟩
theorem mul55 : SAQ_MixedSource.mulE (field ⟨55,by decide⟩) (JGv_WeightsData.cell ⟨55,by decide⟩)=ok product55 := by with_unfolding_all rfl
#print axioms mul55
theorem add55 : FIn_Primitives.add v55 product55=ok v56 := by with_unfolding_all rfl
#print axioms add55
theorem step55 : CheckpointBytes5Output.ofE (state 56)=
    CheckpointBytes5Output.ofE (state 55)+term ⟨55,by decide⟩ := by
  have product := SAQ_MixedSource.mulE_exact _ _ _ JGo_TX2_Message48.canonical55
    (JGv_WeightsData.canonical ⟨55,by decide⟩) mul55
  exact (FIn_Primitives.add_value _ _ _ add55).trans (congrArg (fun t=>CheckpointBytes5Output.ofE v55+t) product.1)
#print axioms step55
def product56 : E := ⟨⟨⟨695914717#u32,408070068#u32⟩,⟨1878487812#u32,1361423683#u32⟩⟩,⟨⟨1828096972#u32,853811794#u32⟩,⟨612073520#u32,1660071755#u32⟩⟩⟩
theorem mul56 : SAQ_MixedSource.mulE (field ⟨56,by decide⟩) (JGv_WeightsData.cell ⟨56,by decide⟩)=ok product56 := by with_unfolding_all rfl
#print axioms mul56
theorem add56 : FIn_Primitives.add v56 product56=ok v57 := by with_unfolding_all rfl
#print axioms add56
theorem step56 : CheckpointBytes5Output.ofE (state 57)=
    CheckpointBytes5Output.ofE (state 56)+term ⟨56,by decide⟩ := by
  have product := SAQ_MixedSource.mulE_exact _ _ _ JGo_TX2_Message56.canonical56
    (JGv_WeightsData.canonical ⟨56,by decide⟩) mul56
  exact (FIn_Primitives.add_value _ _ _ add56).trans (congrArg (fun t=>CheckpointBytes5Output.ofE v56+t) product.1)
#print axioms step56
def product57 : E := ⟨⟨⟨1248297278#u32,1176021439#u32⟩,⟨1574358988#u32,1515291900#u32⟩⟩,⟨⟨1852294088#u32,1598277240#u32⟩,⟨1261662600#u32,1972886181#u32⟩⟩⟩
theorem mul57 : SAQ_MixedSource.mulE (field ⟨57,by decide⟩) (JGv_WeightsData.cell ⟨57,by decide⟩)=ok product57 := by with_unfolding_all rfl
#print axioms mul57
theorem add57 : FIn_Primitives.add v57 product57=ok v58 := by with_unfolding_all rfl
#print axioms add57
theorem step57 : CheckpointBytes5Output.ofE (state 58)=
    CheckpointBytes5Output.ofE (state 57)+term ⟨57,by decide⟩ := by
  have product := SAQ_MixedSource.mulE_exact _ _ _ JGo_TX2_Message56.canonical57
    (JGv_WeightsData.canonical ⟨57,by decide⟩) mul57
  exact (FIn_Primitives.add_value _ _ _ add57).trans (congrArg (fun t=>CheckpointBytes5Output.ofE v57+t) product.1)
#print axioms step57
def product58 : E := ⟨⟨⟨1003439252#u32,2091595910#u32⟩,⟨142145513#u32,953866403#u32⟩⟩,⟨⟨1563924483#u32,107437868#u32⟩,⟨1853443246#u32,862791345#u32⟩⟩⟩
theorem mul58 : SAQ_MixedSource.mulE (field ⟨58,by decide⟩) (JGv_WeightsData.cell ⟨58,by decide⟩)=ok product58 := by with_unfolding_all rfl
#print axioms mul58
theorem add58 : FIn_Primitives.add v58 product58=ok v59 := by with_unfolding_all rfl
#print axioms add58
theorem step58 : CheckpointBytes5Output.ofE (state 59)=
    CheckpointBytes5Output.ofE (state 58)+term ⟨58,by decide⟩ := by
  have product := SAQ_MixedSource.mulE_exact _ _ _ JGo_TX2_Message56.canonical58
    (JGv_WeightsData.canonical ⟨58,by decide⟩) mul58
  exact (FIn_Primitives.add_value _ _ _ add58).trans (congrArg (fun t=>CheckpointBytes5Output.ofE v58+t) product.1)
#print axioms step58
def product59 : E := ⟨⟨⟨459515789#u32,900988093#u32⟩,⟨8501026#u32,1866834179#u32⟩⟩,⟨⟨327684101#u32,1739762532#u32⟩,⟨1376768736#u32,1893464906#u32⟩⟩⟩
theorem mul59 : SAQ_MixedSource.mulE (field ⟨59,by decide⟩) (JGv_WeightsData.cell ⟨59,by decide⟩)=ok product59 := by with_unfolding_all rfl
#print axioms mul59
theorem add59 : FIn_Primitives.add v59 product59=ok v60 := by with_unfolding_all rfl
#print axioms add59
theorem step59 : CheckpointBytes5Output.ofE (state 60)=
    CheckpointBytes5Output.ofE (state 59)+term ⟨59,by decide⟩ := by
  have product := SAQ_MixedSource.mulE_exact _ _ _ JGo_TX2_Message56.canonical59
    (JGv_WeightsData.canonical ⟨59,by decide⟩) mul59
  exact (FIn_Primitives.add_value _ _ _ add59).trans (congrArg (fun t=>CheckpointBytes5Output.ofE v59+t) product.1)
#print axioms step59
def product60 : E := ⟨⟨⟨1824727231#u32,218771892#u32⟩,⟨1506041314#u32,444399727#u32⟩⟩,⟨⟨1090947108#u32,1005225968#u32⟩,⟨1353709914#u32,451065085#u32⟩⟩⟩
theorem mul60 : SAQ_MixedSource.mulE (field ⟨60,by decide⟩) (JGv_WeightsData.cell ⟨60,by decide⟩)=ok product60 := by with_unfolding_all rfl
#print axioms mul60
theorem add60 : FIn_Primitives.add v60 product60=ok v61 := by with_unfolding_all rfl
#print axioms add60
theorem step60 : CheckpointBytes5Output.ofE (state 61)=
    CheckpointBytes5Output.ofE (state 60)+term ⟨60,by decide⟩ := by
  have product := SAQ_MixedSource.mulE_exact _ _ _ JGo_TX2_Message56.canonical60
    (JGv_WeightsData.canonical ⟨60,by decide⟩) mul60
  exact (FIn_Primitives.add_value _ _ _ add60).trans (congrArg (fun t=>CheckpointBytes5Output.ofE v60+t) product.1)
#print axioms step60
def product61 : E := ⟨⟨⟨19883584#u32,1995053319#u32⟩,⟨1759477363#u32,2146021576#u32⟩⟩,⟨⟨1861123138#u32,525543059#u32⟩,⟨1794745738#u32,1002507784#u32⟩⟩⟩
theorem mul61 : SAQ_MixedSource.mulE (field ⟨61,by decide⟩) (JGv_WeightsData.cell ⟨61,by decide⟩)=ok product61 := by with_unfolding_all rfl
#print axioms mul61
theorem add61 : FIn_Primitives.add v61 product61=ok v62 := by with_unfolding_all rfl
#print axioms add61
theorem step61 : CheckpointBytes5Output.ofE (state 62)=
    CheckpointBytes5Output.ofE (state 61)+term ⟨61,by decide⟩ := by
  have product := SAQ_MixedSource.mulE_exact _ _ _ JGo_TX2_Message56.canonical61
    (JGv_WeightsData.canonical ⟨61,by decide⟩) mul61
  exact (FIn_Primitives.add_value _ _ _ add61).trans (congrArg (fun t=>CheckpointBytes5Output.ofE v61+t) product.1)
#print axioms step61
def product62 : E := ⟨⟨⟨1417826895#u32,783317251#u32⟩,⟨358161010#u32,1562194865#u32⟩⟩,⟨⟨1080615533#u32,1496706534#u32⟩,⟨101062587#u32,648468917#u32⟩⟩⟩
theorem mul62 : SAQ_MixedSource.mulE (field ⟨62,by decide⟩) (JGv_WeightsData.cell ⟨62,by decide⟩)=ok product62 := by with_unfolding_all rfl
#print axioms mul62
theorem add62 : FIn_Primitives.add v62 product62=ok v63 := by with_unfolding_all rfl
#print axioms add62
theorem step62 : CheckpointBytes5Output.ofE (state 63)=
    CheckpointBytes5Output.ofE (state 62)+term ⟨62,by decide⟩ := by
  have product := SAQ_MixedSource.mulE_exact _ _ _ JGo_TX2_Message56.canonical62
    (JGv_WeightsData.canonical ⟨62,by decide⟩) mul62
  exact (FIn_Primitives.add_value _ _ _ add62).trans (congrArg (fun t=>CheckpointBytes5Output.ofE v62+t) product.1)
#print axioms step62
def product63 : E := ⟨⟨⟨1512257823#u32,1402018299#u32⟩,⟨336128319#u32,480774880#u32⟩⟩,⟨⟨338811810#u32,1620980307#u32⟩,⟨504036783#u32,1416566980#u32⟩⟩⟩
theorem mul63 : SAQ_MixedSource.mulE (field ⟨63,by decide⟩) (JGv_WeightsData.cell ⟨63,by decide⟩)=ok product63 := by with_unfolding_all rfl
#print axioms mul63
theorem add63 : FIn_Primitives.add v63 product63=ok v64 := by with_unfolding_all rfl
#print axioms add63
theorem step63 : CheckpointBytes5Output.ofE (state 64)=
    CheckpointBytes5Output.ofE (state 63)+term ⟨63,by decide⟩ := by
  have product := SAQ_MixedSource.mulE_exact _ _ _ JGo_TX2_Message56.canonical63
    (JGv_WeightsData.canonical ⟨63,by decide⟩) mul63
  exact (FIn_Primitives.add_value _ _ _ add63).trans (congrArg (fun t=>CheckpointBytes5Output.ofE v63+t) product.1)
#print axioms step63
end AspisR1.JGv_DotProducts3
end
