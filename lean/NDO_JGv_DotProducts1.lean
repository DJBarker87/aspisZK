import NDO_JGv_DotData
import SAQ_MixedSource
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGv_DotProducts1
open Aeneas Aeneas.Std Result
open JGv_DotData
def product16 : E := ⟨⟨⟨844328980#u32,995186272#u32⟩,⟨252576554#u32,1583064596#u32⟩⟩,⟨⟨799844965#u32,839191136#u32⟩,⟨325607518#u32,1643243898#u32⟩⟩⟩
theorem mul16 : SAQ_MixedSource.mulE (field ⟨16,by decide⟩) (JGv_WeightsData.cell ⟨16,by decide⟩)=ok product16 := by with_unfolding_all rfl
#print axioms mul16
theorem add16 : FIn_Primitives.add v16 product16=ok v17 := by with_unfolding_all rfl
#print axioms add16
theorem step16 : CheckpointBytes5Output.ofE (state 17)=
    CheckpointBytes5Output.ofE (state 16)+term ⟨16,by decide⟩ := by
  have product := SAQ_MixedSource.mulE_exact _ _ _ JGo_TX2_Message16.canonical16
    (JGv_WeightsData.canonical ⟨16,by decide⟩) mul16
  exact (FIn_Primitives.add_value _ _ _ add16).trans (congrArg (fun t=>CheckpointBytes5Output.ofE v16+t) product.1)
#print axioms step16
def product17 : E := ⟨⟨⟨77345212#u32,1457764849#u32⟩,⟨172524463#u32,1259158835#u32⟩⟩,⟨⟨1185334262#u32,419542699#u32⟩,⟨1270062759#u32,1100903687#u32⟩⟩⟩
theorem mul17 : SAQ_MixedSource.mulE (field ⟨17,by decide⟩) (JGv_WeightsData.cell ⟨17,by decide⟩)=ok product17 := by with_unfolding_all rfl
#print axioms mul17
theorem add17 : FIn_Primitives.add v17 product17=ok v18 := by with_unfolding_all rfl
#print axioms add17
theorem step17 : CheckpointBytes5Output.ofE (state 18)=
    CheckpointBytes5Output.ofE (state 17)+term ⟨17,by decide⟩ := by
  have product := SAQ_MixedSource.mulE_exact _ _ _ JGo_TX2_Message16.canonical17
    (JGv_WeightsData.canonical ⟨17,by decide⟩) mul17
  exact (FIn_Primitives.add_value _ _ _ add17).trans (congrArg (fun t=>CheckpointBytes5Output.ofE v17+t) product.1)
#print axioms step17
def product18 : E := ⟨⟨⟨128571142#u32,1678794282#u32⟩,⟨939878749#u32,1356758154#u32⟩⟩,⟨⟨1171902922#u32,690844580#u32⟩,⟨1677919742#u32,1475917649#u32⟩⟩⟩
theorem mul18 : SAQ_MixedSource.mulE (field ⟨18,by decide⟩) (JGv_WeightsData.cell ⟨18,by decide⟩)=ok product18 := by with_unfolding_all rfl
#print axioms mul18
theorem add18 : FIn_Primitives.add v18 product18=ok v19 := by with_unfolding_all rfl
#print axioms add18
theorem step18 : CheckpointBytes5Output.ofE (state 19)=
    CheckpointBytes5Output.ofE (state 18)+term ⟨18,by decide⟩ := by
  have product := SAQ_MixedSource.mulE_exact _ _ _ JGo_TX2_Message16.canonical18
    (JGv_WeightsData.canonical ⟨18,by decide⟩) mul18
  exact (FIn_Primitives.add_value _ _ _ add18).trans (congrArg (fun t=>CheckpointBytes5Output.ofE v18+t) product.1)
#print axioms step18
def product19 : E := ⟨⟨⟨1024070424#u32,1201123798#u32⟩,⟨184531985#u32,1696437400#u32⟩⟩,⟨⟨401275810#u32,221944908#u32⟩,⟨1944431071#u32,201197630#u32⟩⟩⟩
theorem mul19 : SAQ_MixedSource.mulE (field ⟨19,by decide⟩) (JGv_WeightsData.cell ⟨19,by decide⟩)=ok product19 := by with_unfolding_all rfl
#print axioms mul19
theorem add19 : FIn_Primitives.add v19 product19=ok v20 := by with_unfolding_all rfl
#print axioms add19
theorem step19 : CheckpointBytes5Output.ofE (state 20)=
    CheckpointBytes5Output.ofE (state 19)+term ⟨19,by decide⟩ := by
  have product := SAQ_MixedSource.mulE_exact _ _ _ JGo_TX2_Message16.canonical19
    (JGv_WeightsData.canonical ⟨19,by decide⟩) mul19
  exact (FIn_Primitives.add_value _ _ _ add19).trans (congrArg (fun t=>CheckpointBytes5Output.ofE v19+t) product.1)
#print axioms step19
def product20 : E := ⟨⟨⟨1208477860#u32,750333784#u32⟩,⟨1100059409#u32,468147857#u32⟩⟩,⟨⟨218937925#u32,1778837512#u32⟩,⟨1032015099#u32,417571512#u32⟩⟩⟩
theorem mul20 : SAQ_MixedSource.mulE (field ⟨20,by decide⟩) (JGv_WeightsData.cell ⟨20,by decide⟩)=ok product20 := by with_unfolding_all rfl
#print axioms mul20
theorem add20 : FIn_Primitives.add v20 product20=ok v21 := by with_unfolding_all rfl
#print axioms add20
theorem step20 : CheckpointBytes5Output.ofE (state 21)=
    CheckpointBytes5Output.ofE (state 20)+term ⟨20,by decide⟩ := by
  have product := SAQ_MixedSource.mulE_exact _ _ _ JGo_TX2_Message16.canonical20
    (JGv_WeightsData.canonical ⟨20,by decide⟩) mul20
  exact (FIn_Primitives.add_value _ _ _ add20).trans (congrArg (fun t=>CheckpointBytes5Output.ofE v20+t) product.1)
#print axioms step20
def product21 : E := ⟨⟨⟨1528363938#u32,1765306136#u32⟩,⟨70618909#u32,815977698#u32⟩⟩,⟨⟨138106399#u32,1487903385#u32⟩,⟨1928886151#u32,769786836#u32⟩⟩⟩
theorem mul21 : SAQ_MixedSource.mulE (field ⟨21,by decide⟩) (JGv_WeightsData.cell ⟨21,by decide⟩)=ok product21 := by with_unfolding_all rfl
#print axioms mul21
theorem add21 : FIn_Primitives.add v21 product21=ok v22 := by with_unfolding_all rfl
#print axioms add21
theorem step21 : CheckpointBytes5Output.ofE (state 22)=
    CheckpointBytes5Output.ofE (state 21)+term ⟨21,by decide⟩ := by
  have product := SAQ_MixedSource.mulE_exact _ _ _ JGo_TX2_Message16.canonical21
    (JGv_WeightsData.canonical ⟨21,by decide⟩) mul21
  exact (FIn_Primitives.add_value _ _ _ add21).trans (congrArg (fun t=>CheckpointBytes5Output.ofE v21+t) product.1)
#print axioms step21
def product22 : E := ⟨⟨⟨1473464540#u32,1151553250#u32⟩,⟨1435059202#u32,1246203476#u32⟩⟩,⟨⟨226766853#u32,1435727962#u32⟩,⟨1011199103#u32,573521406#u32⟩⟩⟩
theorem mul22 : SAQ_MixedSource.mulE (field ⟨22,by decide⟩) (JGv_WeightsData.cell ⟨22,by decide⟩)=ok product22 := by with_unfolding_all rfl
#print axioms mul22
theorem add22 : FIn_Primitives.add v22 product22=ok v23 := by with_unfolding_all rfl
#print axioms add22
theorem step22 : CheckpointBytes5Output.ofE (state 23)=
    CheckpointBytes5Output.ofE (state 22)+term ⟨22,by decide⟩ := by
  have product := SAQ_MixedSource.mulE_exact _ _ _ JGo_TX2_Message16.canonical22
    (JGv_WeightsData.canonical ⟨22,by decide⟩) mul22
  exact (FIn_Primitives.add_value _ _ _ add22).trans (congrArg (fun t=>CheckpointBytes5Output.ofE v22+t) product.1)
#print axioms step22
def product23 : E := ⟨⟨⟨977335294#u32,139505722#u32⟩,⟨1699717825#u32,967999346#u32⟩⟩,⟨⟨1428628456#u32,287737306#u32⟩,⟨828155245#u32,218439059#u32⟩⟩⟩
theorem mul23 : SAQ_MixedSource.mulE (field ⟨23,by decide⟩) (JGv_WeightsData.cell ⟨23,by decide⟩)=ok product23 := by with_unfolding_all rfl
#print axioms mul23
theorem add23 : FIn_Primitives.add v23 product23=ok v24 := by with_unfolding_all rfl
#print axioms add23
theorem step23 : CheckpointBytes5Output.ofE (state 24)=
    CheckpointBytes5Output.ofE (state 23)+term ⟨23,by decide⟩ := by
  have product := SAQ_MixedSource.mulE_exact _ _ _ JGo_TX2_Message16.canonical23
    (JGv_WeightsData.canonical ⟨23,by decide⟩) mul23
  exact (FIn_Primitives.add_value _ _ _ add23).trans (congrArg (fun t=>CheckpointBytes5Output.ofE v23+t) product.1)
#print axioms step23
def product24 : E := ⟨⟨⟨1017821289#u32,1850155658#u32⟩,⟨353489717#u32,1987867973#u32⟩⟩,⟨⟨1725442256#u32,1960709923#u32⟩,⟨1378273145#u32,31821905#u32⟩⟩⟩
theorem mul24 : SAQ_MixedSource.mulE (field ⟨24,by decide⟩) (JGv_WeightsData.cell ⟨24,by decide⟩)=ok product24 := by with_unfolding_all rfl
#print axioms mul24
theorem add24 : FIn_Primitives.add v24 product24=ok v25 := by with_unfolding_all rfl
#print axioms add24
theorem step24 : CheckpointBytes5Output.ofE (state 25)=
    CheckpointBytes5Output.ofE (state 24)+term ⟨24,by decide⟩ := by
  have product := SAQ_MixedSource.mulE_exact _ _ _ JGo_TX2_Message24.canonical24
    (JGv_WeightsData.canonical ⟨24,by decide⟩) mul24
  exact (FIn_Primitives.add_value _ _ _ add24).trans (congrArg (fun t=>CheckpointBytes5Output.ofE v24+t) product.1)
#print axioms step24
def product25 : E := ⟨⟨⟨503820704#u32,1344758553#u32⟩,⟨1009086144#u32,1333823939#u32⟩⟩,⟨⟨1069373046#u32,1136176771#u32⟩,⟨1861399970#u32,126492113#u32⟩⟩⟩
theorem mul25 : SAQ_MixedSource.mulE (field ⟨25,by decide⟩) (JGv_WeightsData.cell ⟨25,by decide⟩)=ok product25 := by with_unfolding_all rfl
#print axioms mul25
theorem add25 : FIn_Primitives.add v25 product25=ok v26 := by with_unfolding_all rfl
#print axioms add25
theorem step25 : CheckpointBytes5Output.ofE (state 26)=
    CheckpointBytes5Output.ofE (state 25)+term ⟨25,by decide⟩ := by
  have product := SAQ_MixedSource.mulE_exact _ _ _ JGo_TX2_Message24.canonical25
    (JGv_WeightsData.canonical ⟨25,by decide⟩) mul25
  exact (FIn_Primitives.add_value _ _ _ add25).trans (congrArg (fun t=>CheckpointBytes5Output.ofE v25+t) product.1)
#print axioms step25
def product26 : E := ⟨⟨⟨720303873#u32,1044778190#u32⟩,⟨1273821243#u32,285179305#u32⟩⟩,⟨⟨1839361704#u32,1832828725#u32⟩,⟨604869019#u32,441230219#u32⟩⟩⟩
theorem mul26 : SAQ_MixedSource.mulE (field ⟨26,by decide⟩) (JGv_WeightsData.cell ⟨26,by decide⟩)=ok product26 := by with_unfolding_all rfl
#print axioms mul26
theorem add26 : FIn_Primitives.add v26 product26=ok v27 := by with_unfolding_all rfl
#print axioms add26
theorem step26 : CheckpointBytes5Output.ofE (state 27)=
    CheckpointBytes5Output.ofE (state 26)+term ⟨26,by decide⟩ := by
  have product := SAQ_MixedSource.mulE_exact _ _ _ JGo_TX2_Message24.canonical26
    (JGv_WeightsData.canonical ⟨26,by decide⟩) mul26
  exact (FIn_Primitives.add_value _ _ _ add26).trans (congrArg (fun t=>CheckpointBytes5Output.ofE v26+t) product.1)
#print axioms step26
def product27 : E := ⟨⟨⟨1775972299#u32,1584600525#u32⟩,⟨209749385#u32,1863320461#u32⟩⟩,⟨⟨716457795#u32,253896882#u32⟩,⟨983875992#u32,567872768#u32⟩⟩⟩
theorem mul27 : SAQ_MixedSource.mulE (field ⟨27,by decide⟩) (JGv_WeightsData.cell ⟨27,by decide⟩)=ok product27 := by with_unfolding_all rfl
#print axioms mul27
theorem add27 : FIn_Primitives.add v27 product27=ok v28 := by with_unfolding_all rfl
#print axioms add27
theorem step27 : CheckpointBytes5Output.ofE (state 28)=
    CheckpointBytes5Output.ofE (state 27)+term ⟨27,by decide⟩ := by
  have product := SAQ_MixedSource.mulE_exact _ _ _ JGo_TX2_Message24.canonical27
    (JGv_WeightsData.canonical ⟨27,by decide⟩) mul27
  exact (FIn_Primitives.add_value _ _ _ add27).trans (congrArg (fun t=>CheckpointBytes5Output.ofE v27+t) product.1)
#print axioms step27
def product28 : E := ⟨⟨⟨665215724#u32,189274208#u32⟩,⟨1946608064#u32,1376124482#u32⟩⟩,⟨⟨123175940#u32,1262248591#u32⟩,⟨619314272#u32,1334567681#u32⟩⟩⟩
theorem mul28 : SAQ_MixedSource.mulE (field ⟨28,by decide⟩) (JGv_WeightsData.cell ⟨28,by decide⟩)=ok product28 := by with_unfolding_all rfl
#print axioms mul28
theorem add28 : FIn_Primitives.add v28 product28=ok v29 := by with_unfolding_all rfl
#print axioms add28
theorem step28 : CheckpointBytes5Output.ofE (state 29)=
    CheckpointBytes5Output.ofE (state 28)+term ⟨28,by decide⟩ := by
  have product := SAQ_MixedSource.mulE_exact _ _ _ JGo_TX2_Message24.canonical28
    (JGv_WeightsData.canonical ⟨28,by decide⟩) mul28
  exact (FIn_Primitives.add_value _ _ _ add28).trans (congrArg (fun t=>CheckpointBytes5Output.ofE v28+t) product.1)
#print axioms step28
def product29 : E := ⟨⟨⟨1426374690#u32,163093657#u32⟩,⟨1774381843#u32,1074201678#u32⟩⟩,⟨⟨1325038405#u32,463429666#u32⟩,⟨1804871027#u32,1376729156#u32⟩⟩⟩
theorem mul29 : SAQ_MixedSource.mulE (field ⟨29,by decide⟩) (JGv_WeightsData.cell ⟨29,by decide⟩)=ok product29 := by with_unfolding_all rfl
#print axioms mul29
theorem add29 : FIn_Primitives.add v29 product29=ok v30 := by with_unfolding_all rfl
#print axioms add29
theorem step29 : CheckpointBytes5Output.ofE (state 30)=
    CheckpointBytes5Output.ofE (state 29)+term ⟨29,by decide⟩ := by
  have product := SAQ_MixedSource.mulE_exact _ _ _ JGo_TX2_Message24.canonical29
    (JGv_WeightsData.canonical ⟨29,by decide⟩) mul29
  exact (FIn_Primitives.add_value _ _ _ add29).trans (congrArg (fun t=>CheckpointBytes5Output.ofE v29+t) product.1)
#print axioms step29
def product30 : E := ⟨⟨⟨1137294402#u32,1598079197#u32⟩,⟨583307363#u32,490611542#u32⟩⟩,⟨⟨356651486#u32,928697917#u32⟩,⟨1349687517#u32,778803032#u32⟩⟩⟩
theorem mul30 : SAQ_MixedSource.mulE (field ⟨30,by decide⟩) (JGv_WeightsData.cell ⟨30,by decide⟩)=ok product30 := by with_unfolding_all rfl
#print axioms mul30
theorem add30 : FIn_Primitives.add v30 product30=ok v31 := by with_unfolding_all rfl
#print axioms add30
theorem step30 : CheckpointBytes5Output.ofE (state 31)=
    CheckpointBytes5Output.ofE (state 30)+term ⟨30,by decide⟩ := by
  have product := SAQ_MixedSource.mulE_exact _ _ _ JGo_TX2_Message24.canonical30
    (JGv_WeightsData.canonical ⟨30,by decide⟩) mul30
  exact (FIn_Primitives.add_value _ _ _ add30).trans (congrArg (fun t=>CheckpointBytes5Output.ofE v30+t) product.1)
#print axioms step30
def product31 : E := ⟨⟨⟨2000204012#u32,1666352081#u32⟩,⟨375571863#u32,516968481#u32⟩⟩,⟨⟨569985003#u32,1971343313#u32⟩,⟨1626814353#u32,1733617326#u32⟩⟩⟩
theorem mul31 : SAQ_MixedSource.mulE (field ⟨31,by decide⟩) (JGv_WeightsData.cell ⟨31,by decide⟩)=ok product31 := by with_unfolding_all rfl
#print axioms mul31
theorem add31 : FIn_Primitives.add v31 product31=ok v32 := by with_unfolding_all rfl
#print axioms add31
theorem step31 : CheckpointBytes5Output.ofE (state 32)=
    CheckpointBytes5Output.ofE (state 31)+term ⟨31,by decide⟩ := by
  have product := SAQ_MixedSource.mulE_exact _ _ _ JGo_TX2_Message24.canonical31
    (JGv_WeightsData.canonical ⟨31,by decide⟩) mul31
  exact (FIn_Primitives.add_value _ _ _ add31).trans (congrArg (fun t=>CheckpointBytes5Output.ofE v31+t) product.1)
#print axioms step31
end AspisR1.JGv_DotProducts1
end
