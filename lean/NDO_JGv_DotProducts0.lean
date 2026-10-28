import NDO_JGv_DotData
import SAQ_MixedSource
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGv_DotProducts0
open Aeneas Aeneas.Std Result
open JGv_DotData
def product00 : E := ⟨⟨⟨706778933#u32,1572153114#u32⟩,⟨1515725800#u32,1227609308#u32⟩⟩,⟨⟨707364273#u32,1606918087#u32⟩,⟨771864436#u32,1556141296#u32⟩⟩⟩
theorem mul00 : SAQ_MixedSource.mulE (field ⟨0,by decide⟩) (JGv_WeightsData.cell ⟨0,by decide⟩)=ok product00 := by with_unfolding_all rfl
#print axioms mul00
theorem add00 : FIn_Primitives.add v00 product00=ok v01 := by with_unfolding_all rfl
#print axioms add00
theorem step00 : CheckpointBytes5Output.ofE (state 1)=
    CheckpointBytes5Output.ofE (state 0)+term ⟨0,by decide⟩ := by
  have product := SAQ_MixedSource.mulE_exact _ _ _ JGo_TX2_Message00.canonical00
    (JGv_WeightsData.canonical ⟨0,by decide⟩) mul00
  exact (FIn_Primitives.add_value _ _ _ add00).trans (congrArg (fun t=>CheckpointBytes5Output.ofE v00+t) product.1)
#print axioms step00
def product01 : E := ⟨⟨⟨2006104894#u32,1190516386#u32⟩,⟨769481025#u32,60084431#u32⟩⟩,⟨⟨35653721#u32,519555190#u32⟩,⟨2107116998#u32,1965094650#u32⟩⟩⟩
theorem mul01 : SAQ_MixedSource.mulE (field ⟨1,by decide⟩) (JGv_WeightsData.cell ⟨1,by decide⟩)=ok product01 := by with_unfolding_all rfl
#print axioms mul01
theorem add01 : FIn_Primitives.add v01 product01=ok v02 := by with_unfolding_all rfl
#print axioms add01
theorem step01 : CheckpointBytes5Output.ofE (state 2)=
    CheckpointBytes5Output.ofE (state 1)+term ⟨1,by decide⟩ := by
  have product := SAQ_MixedSource.mulE_exact _ _ _ JGo_TX2_Message00.canonical01
    (JGv_WeightsData.canonical ⟨1,by decide⟩) mul01
  exact (FIn_Primitives.add_value _ _ _ add01).trans (congrArg (fun t=>CheckpointBytes5Output.ofE v01+t) product.1)
#print axioms step01
def product02 : E := ⟨⟨⟨432709159#u32,2000434460#u32⟩,⟨645418130#u32,541460461#u32⟩⟩,⟨⟨2049203618#u32,2143001788#u32⟩,⟨1866886545#u32,340514857#u32⟩⟩⟩
theorem mul02 : SAQ_MixedSource.mulE (field ⟨2,by decide⟩) (JGv_WeightsData.cell ⟨2,by decide⟩)=ok product02 := by with_unfolding_all rfl
#print axioms mul02
theorem add02 : FIn_Primitives.add v02 product02=ok v03 := by with_unfolding_all rfl
#print axioms add02
theorem step02 : CheckpointBytes5Output.ofE (state 3)=
    CheckpointBytes5Output.ofE (state 2)+term ⟨2,by decide⟩ := by
  have product := SAQ_MixedSource.mulE_exact _ _ _ JGo_TX2_Message00.canonical02
    (JGv_WeightsData.canonical ⟨2,by decide⟩) mul02
  exact (FIn_Primitives.add_value _ _ _ add02).trans (congrArg (fun t=>CheckpointBytes5Output.ofE v02+t) product.1)
#print axioms step02
def product03 : E := ⟨⟨⟨61692656#u32,841597520#u32⟩,⟨1512819682#u32,1301404679#u32⟩⟩,⟨⟨1965909968#u32,920180662#u32⟩,⟨1174809785#u32,981317401#u32⟩⟩⟩
theorem mul03 : SAQ_MixedSource.mulE (field ⟨3,by decide⟩) (JGv_WeightsData.cell ⟨3,by decide⟩)=ok product03 := by with_unfolding_all rfl
#print axioms mul03
theorem add03 : FIn_Primitives.add v03 product03=ok v04 := by with_unfolding_all rfl
#print axioms add03
theorem step03 : CheckpointBytes5Output.ofE (state 4)=
    CheckpointBytes5Output.ofE (state 3)+term ⟨3,by decide⟩ := by
  have product := SAQ_MixedSource.mulE_exact _ _ _ JGo_TX2_Message00.canonical03
    (JGv_WeightsData.canonical ⟨3,by decide⟩) mul03
  exact (FIn_Primitives.add_value _ _ _ add03).trans (congrArg (fun t=>CheckpointBytes5Output.ofE v03+t) product.1)
#print axioms step03
def product04 : E := ⟨⟨⟨856328255#u32,1987580495#u32⟩,⟨1153289263#u32,1035759753#u32⟩⟩,⟨⟨238689547#u32,977064243#u32⟩,⟨473627190#u32,1511599611#u32⟩⟩⟩
theorem mul04 : SAQ_MixedSource.mulE (field ⟨4,by decide⟩) (JGv_WeightsData.cell ⟨4,by decide⟩)=ok product04 := by with_unfolding_all rfl
#print axioms mul04
theorem add04 : FIn_Primitives.add v04 product04=ok v05 := by with_unfolding_all rfl
#print axioms add04
theorem step04 : CheckpointBytes5Output.ofE (state 5)=
    CheckpointBytes5Output.ofE (state 4)+term ⟨4,by decide⟩ := by
  have product := SAQ_MixedSource.mulE_exact _ _ _ JGo_TX2_Message00.canonical04
    (JGv_WeightsData.canonical ⟨4,by decide⟩) mul04
  exact (FIn_Primitives.add_value _ _ _ add04).trans (congrArg (fun t=>CheckpointBytes5Output.ofE v04+t) product.1)
#print axioms step04
def product05 : E := ⟨⟨⟨1743067377#u32,151652109#u32⟩,⟨2064537401#u32,742712501#u32⟩⟩,⟨⟨797742022#u32,318239738#u32⟩,⟨661761575#u32,530866013#u32⟩⟩⟩
theorem mul05 : SAQ_MixedSource.mulE (field ⟨5,by decide⟩) (JGv_WeightsData.cell ⟨5,by decide⟩)=ok product05 := by with_unfolding_all rfl
#print axioms mul05
theorem add05 : FIn_Primitives.add v05 product05=ok v06 := by with_unfolding_all rfl
#print axioms add05
theorem step05 : CheckpointBytes5Output.ofE (state 6)=
    CheckpointBytes5Output.ofE (state 5)+term ⟨5,by decide⟩ := by
  have product := SAQ_MixedSource.mulE_exact _ _ _ JGo_TX2_Message00.canonical05
    (JGv_WeightsData.canonical ⟨5,by decide⟩) mul05
  exact (FIn_Primitives.add_value _ _ _ add05).trans (congrArg (fun t=>CheckpointBytes5Output.ofE v05+t) product.1)
#print axioms step05
def product06 : E := ⟨⟨⟨1615839537#u32,950499955#u32⟩,⟨268855192#u32,83102817#u32⟩⟩,⟨⟨312187370#u32,137590143#u32⟩,⟨2118518907#u32,1994605394#u32⟩⟩⟩
theorem mul06 : SAQ_MixedSource.mulE (field ⟨6,by decide⟩) (JGv_WeightsData.cell ⟨6,by decide⟩)=ok product06 := by with_unfolding_all rfl
#print axioms mul06
theorem add06 : FIn_Primitives.add v06 product06=ok v07 := by with_unfolding_all rfl
#print axioms add06
theorem step06 : CheckpointBytes5Output.ofE (state 7)=
    CheckpointBytes5Output.ofE (state 6)+term ⟨6,by decide⟩ := by
  have product := SAQ_MixedSource.mulE_exact _ _ _ JGo_TX2_Message00.canonical06
    (JGv_WeightsData.canonical ⟨6,by decide⟩) mul06
  exact (FIn_Primitives.add_value _ _ _ add06).trans (congrArg (fun t=>CheckpointBytes5Output.ofE v06+t) product.1)
#print axioms step06
def product07 : E := ⟨⟨⟨650830550#u32,1082281518#u32⟩,⟨250003623#u32,360820693#u32⟩⟩,⟨⟨249549023#u32,974905595#u32⟩,⟨1367635513#u32,747940211#u32⟩⟩⟩
theorem mul07 : SAQ_MixedSource.mulE (field ⟨7,by decide⟩) (JGv_WeightsData.cell ⟨7,by decide⟩)=ok product07 := by with_unfolding_all rfl
#print axioms mul07
theorem add07 : FIn_Primitives.add v07 product07=ok v08 := by with_unfolding_all rfl
#print axioms add07
theorem step07 : CheckpointBytes5Output.ofE (state 8)=
    CheckpointBytes5Output.ofE (state 7)+term ⟨7,by decide⟩ := by
  have product := SAQ_MixedSource.mulE_exact _ _ _ JGo_TX2_Message00.canonical07
    (JGv_WeightsData.canonical ⟨7,by decide⟩) mul07
  exact (FIn_Primitives.add_value _ _ _ add07).trans (congrArg (fun t=>CheckpointBytes5Output.ofE v07+t) product.1)
#print axioms step07
def product08 : E := ⟨⟨⟨2079759078#u32,2136362254#u32⟩,⟨634744872#u32,980817391#u32⟩⟩,⟨⟨1299163855#u32,1363311026#u32⟩,⟨734374136#u32,230551394#u32⟩⟩⟩
theorem mul08 : SAQ_MixedSource.mulE (field ⟨8,by decide⟩) (JGv_WeightsData.cell ⟨8,by decide⟩)=ok product08 := by with_unfolding_all rfl
#print axioms mul08
theorem add08 : FIn_Primitives.add v08 product08=ok v09 := by with_unfolding_all rfl
#print axioms add08
theorem step08 : CheckpointBytes5Output.ofE (state 9)=
    CheckpointBytes5Output.ofE (state 8)+term ⟨8,by decide⟩ := by
  have product := SAQ_MixedSource.mulE_exact _ _ _ JGo_TX2_Message08.canonical08
    (JGv_WeightsData.canonical ⟨8,by decide⟩) mul08
  exact (FIn_Primitives.add_value _ _ _ add08).trans (congrArg (fun t=>CheckpointBytes5Output.ofE v08+t) product.1)
#print axioms step08
def product09 : E := ⟨⟨⟨175009945#u32,215574666#u32⟩,⟨175450319#u32,369640763#u32⟩⟩,⟨⟨185888301#u32,1709279697#u32⟩,⟨971650214#u32,1232830954#u32⟩⟩⟩
theorem mul09 : SAQ_MixedSource.mulE (field ⟨9,by decide⟩) (JGv_WeightsData.cell ⟨9,by decide⟩)=ok product09 := by with_unfolding_all rfl
#print axioms mul09
theorem add09 : FIn_Primitives.add v09 product09=ok v10 := by with_unfolding_all rfl
#print axioms add09
theorem step09 : CheckpointBytes5Output.ofE (state 10)=
    CheckpointBytes5Output.ofE (state 9)+term ⟨9,by decide⟩ := by
  have product := SAQ_MixedSource.mulE_exact _ _ _ JGo_TX2_Message08.canonical09
    (JGv_WeightsData.canonical ⟨9,by decide⟩) mul09
  exact (FIn_Primitives.add_value _ _ _ add09).trans (congrArg (fun t=>CheckpointBytes5Output.ofE v09+t) product.1)
#print axioms step09
def product10 : E := ⟨⟨⟨567463424#u32,353202267#u32⟩,⟨1428022199#u32,894652664#u32⟩⟩,⟨⟨297919915#u32,1113341394#u32⟩,⟨2004533612#u32,643731604#u32⟩⟩⟩
theorem mul10 : SAQ_MixedSource.mulE (field ⟨10,by decide⟩) (JGv_WeightsData.cell ⟨10,by decide⟩)=ok product10 := by with_unfolding_all rfl
#print axioms mul10
theorem add10 : FIn_Primitives.add v10 product10=ok v11 := by with_unfolding_all rfl
#print axioms add10
theorem step10 : CheckpointBytes5Output.ofE (state 11)=
    CheckpointBytes5Output.ofE (state 10)+term ⟨10,by decide⟩ := by
  have product := SAQ_MixedSource.mulE_exact _ _ _ JGo_TX2_Message08.canonical10
    (JGv_WeightsData.canonical ⟨10,by decide⟩) mul10
  exact (FIn_Primitives.add_value _ _ _ add10).trans (congrArg (fun t=>CheckpointBytes5Output.ofE v10+t) product.1)
#print axioms step10
def product11 : E := ⟨⟨⟨21604881#u32,1249611223#u32⟩,⟨1326168931#u32,1884201415#u32⟩⟩,⟨⟨959957320#u32,862438818#u32⟩,⟨1496899772#u32,2035229847#u32⟩⟩⟩
theorem mul11 : SAQ_MixedSource.mulE (field ⟨11,by decide⟩) (JGv_WeightsData.cell ⟨11,by decide⟩)=ok product11 := by with_unfolding_all rfl
#print axioms mul11
theorem add11 : FIn_Primitives.add v11 product11=ok v12 := by with_unfolding_all rfl
#print axioms add11
theorem step11 : CheckpointBytes5Output.ofE (state 12)=
    CheckpointBytes5Output.ofE (state 11)+term ⟨11,by decide⟩ := by
  have product := SAQ_MixedSource.mulE_exact _ _ _ JGo_TX2_Message08.canonical11
    (JGv_WeightsData.canonical ⟨11,by decide⟩) mul11
  exact (FIn_Primitives.add_value _ _ _ add11).trans (congrArg (fun t=>CheckpointBytes5Output.ofE v11+t) product.1)
#print axioms step11
def product12 : E := ⟨⟨⟨675448448#u32,449192943#u32⟩,⟨536461224#u32,2012700486#u32⟩⟩,⟨⟨1525843664#u32,415710816#u32⟩,⟨1499363296#u32,1570845153#u32⟩⟩⟩
theorem mul12 : SAQ_MixedSource.mulE (field ⟨12,by decide⟩) (JGv_WeightsData.cell ⟨12,by decide⟩)=ok product12 := by with_unfolding_all rfl
#print axioms mul12
theorem add12 : FIn_Primitives.add v12 product12=ok v13 := by with_unfolding_all rfl
#print axioms add12
theorem step12 : CheckpointBytes5Output.ofE (state 13)=
    CheckpointBytes5Output.ofE (state 12)+term ⟨12,by decide⟩ := by
  have product := SAQ_MixedSource.mulE_exact _ _ _ JGo_TX2_Message08.canonical12
    (JGv_WeightsData.canonical ⟨12,by decide⟩) mul12
  exact (FIn_Primitives.add_value _ _ _ add12).trans (congrArg (fun t=>CheckpointBytes5Output.ofE v12+t) product.1)
#print axioms step12
def product13 : E := ⟨⟨⟨1800924992#u32,878205223#u32⟩,⟨362522142#u32,1817971349#u32⟩⟩,⟨⟨938948069#u32,1839904656#u32⟩,⟨800831885#u32,1144162643#u32⟩⟩⟩
theorem mul13 : SAQ_MixedSource.mulE (field ⟨13,by decide⟩) (JGv_WeightsData.cell ⟨13,by decide⟩)=ok product13 := by with_unfolding_all rfl
#print axioms mul13
theorem add13 : FIn_Primitives.add v13 product13=ok v14 := by with_unfolding_all rfl
#print axioms add13
theorem step13 : CheckpointBytes5Output.ofE (state 14)=
    CheckpointBytes5Output.ofE (state 13)+term ⟨13,by decide⟩ := by
  have product := SAQ_MixedSource.mulE_exact _ _ _ JGo_TX2_Message08.canonical13
    (JGv_WeightsData.canonical ⟨13,by decide⟩) mul13
  exact (FIn_Primitives.add_value _ _ _ add13).trans (congrArg (fun t=>CheckpointBytes5Output.ofE v13+t) product.1)
#print axioms step13
def product14 : E := ⟨⟨⟨1537044081#u32,1784659596#u32⟩,⟨1969221347#u32,586892698#u32⟩⟩,⟨⟨1830770726#u32,2027266116#u32⟩,⟨1196531532#u32,721565616#u32⟩⟩⟩
theorem mul14 : SAQ_MixedSource.mulE (field ⟨14,by decide⟩) (JGv_WeightsData.cell ⟨14,by decide⟩)=ok product14 := by with_unfolding_all rfl
#print axioms mul14
theorem add14 : FIn_Primitives.add v14 product14=ok v15 := by with_unfolding_all rfl
#print axioms add14
theorem step14 : CheckpointBytes5Output.ofE (state 15)=
    CheckpointBytes5Output.ofE (state 14)+term ⟨14,by decide⟩ := by
  have product := SAQ_MixedSource.mulE_exact _ _ _ JGo_TX2_Message08.canonical14
    (JGv_WeightsData.canonical ⟨14,by decide⟩) mul14
  exact (FIn_Primitives.add_value _ _ _ add14).trans (congrArg (fun t=>CheckpointBytes5Output.ofE v14+t) product.1)
#print axioms step14
def product15 : E := ⟨⟨⟨1145550395#u32,561911970#u32⟩,⟨1536082508#u32,503376173#u32⟩⟩,⟨⟨283086574#u32,540146306#u32⟩,⟨694531542#u32,1433290179#u32⟩⟩⟩
theorem mul15 : SAQ_MixedSource.mulE (field ⟨15,by decide⟩) (JGv_WeightsData.cell ⟨15,by decide⟩)=ok product15 := by with_unfolding_all rfl
#print axioms mul15
theorem add15 : FIn_Primitives.add v15 product15=ok v16 := by with_unfolding_all rfl
#print axioms add15
theorem step15 : CheckpointBytes5Output.ofE (state 16)=
    CheckpointBytes5Output.ofE (state 15)+term ⟨15,by decide⟩ := by
  have product := SAQ_MixedSource.mulE_exact _ _ _ JGo_TX2_Message08.canonical15
    (JGv_WeightsData.canonical ⟨15,by decide⟩) mul15
  exact (FIn_Primitives.add_value _ _ _ add15).trans (congrArg (fun t=>CheckpointBytes5Output.ofE v15+t) product.1)
#print axioms step15
end AspisR1.JGv_DotProducts0
end
