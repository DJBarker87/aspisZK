import JGp_Active
import JGp_Allocation
import JGp_BatchInput
import JGp_ClosedGeometry
import JGp_CurrentQueries
import JGp_CurrentRoots
import JGp_FoldedRead
import JGp_Geo0
import JGp_Geo1
import JGp_Geo2
import JGp_Geo3
import JGp_Geo4
import JGp_Geo5
import JGp_Geo6
import JGp_Geo7
import JGp_Geo8
import JGp_Geo9
import JGp_Geometry
import JGp_Keys0
import JGp_Keys1
import JGp_Keys2
import JGp_Line0
import JGp_Line1
import JGp_Line2
import JGp_Line3
import JGp_Line4
import JGp_Line5
import JGp_Line6
import JGp_Line7
import JGp_Line8
import JGp_Line9
import JGp_Loop
import JGp_Opening0
import JGp_Opening1
import JGp_Opening2
import JGp_Opening3
import JGp_Opening4
import JGp_Opening5
import JGp_Opening6
import JGp_Opening7
import JGp_Opening8
import JGp_Opening9
import JGp_PreBatchFixture
import JGp_Prepare
import JGp_PrepareCuts
import JGp_PrepareInspect
import JGp_PrepareLayout
import JGp_PrepareReads
import JGp_PreparedQueries
import JGp_QueryCalls
import JGp_QueryNumeric
import JGp_Recombine
import JGp_RecombinedReads
import JGp_Row0
import JGp_Row1
import JGp_Row2
import JGp_Row3
import JGp_Row4
import JGp_Row5
import JGp_Row6
import JGp_Row7
import JGp_Row8
import JGp_Row9
import JGp_Rows
import JGp_Seeds
import JGp_SemanticIdentity
import JGp_Shape
import JGp_Slot0
import JGp_Slot1
import JGp_Slot2
import JGp_TX1Geometry
import JGp_TX1Initial
import JGp_ValuesIdentity
import JGn_FinalAudit
import FJp_Top
set_option autoImplicit false
#print axioms AspisR1.JGp_Active.source
#print axioms AspisR1.JGp_Allocation.allocated
#print axioms AspisR1.JGp_BatchInput.source
#print axioms AspisR1.JGp_ClosedGeometry.inhabited
#print axioms AspisR1.JGp_CurrentQueries.source
#print axioms AspisR1.JGp_CurrentRoots.source
#print axioms AspisR1.JGp_FoldedRead.range
#print axioms AspisR1.JGp_FoldedRead.copy
#print axioms AspisR1.JGp_Geo0.source0
#print axioms AspisR1.JGp_Geo0.source1
#print axioms AspisR1.JGp_Geo0.source2
#print axioms AspisR1.JGp_Geo1.source0
#print axioms AspisR1.JGp_Geo1.source1
#print axioms AspisR1.JGp_Geo1.source2
#print axioms AspisR1.JGp_Geo2.source0
#print axioms AspisR1.JGp_Geo2.source1
#print axioms AspisR1.JGp_Geo2.source2
#print axioms AspisR1.JGp_Geo3.source0
#print axioms AspisR1.JGp_Geo3.source1
#print axioms AspisR1.JGp_Geo3.source2
#print axioms AspisR1.JGp_Geo4.source0
#print axioms AspisR1.JGp_Geo4.source1
#print axioms AspisR1.JGp_Geo4.source2
#print axioms AspisR1.JGp_Geo5.source0
#print axioms AspisR1.JGp_Geo5.source1
#print axioms AspisR1.JGp_Geo5.source2
#print axioms AspisR1.JGp_Geo6.source0
#print axioms AspisR1.JGp_Geo6.source1
#print axioms AspisR1.JGp_Geo6.source2
#print axioms AspisR1.JGp_Geo7.source0
#print axioms AspisR1.JGp_Geo7.source1
#print axioms AspisR1.JGp_Geo7.source2
#print axioms AspisR1.JGp_Geo8.source0
#print axioms AspisR1.JGp_Geo8.source1
#print axioms AspisR1.JGp_Geo8.source2
#print axioms AspisR1.JGp_Geo9.source0
#print axioms AspisR1.JGp_Geo9.source1
#print axioms AspisR1.JGp_Geo9.source2
#print axioms AspisR1.JGp_Geometry.meaning
#print axioms AspisR1.JGp_Geometry.selected
#print axioms AspisR1.JGp_Geometry.source
#print axioms AspisR1.JGp_Geometry.native
#print axioms AspisR1.JGp_Geometry.stage
#print axioms AspisR1.JGp_Keys0.content
#print axioms AspisR1.JGp_Keys0.source
#print axioms AspisR1.JGp_Keys1.content
#print axioms AspisR1.JGp_Keys1.source
#print axioms AspisR1.JGp_Keys2.content
#print axioms AspisR1.JGp_Keys2.source
#print axioms AspisR1.JGp_Line0.source0
#print axioms AspisR1.JGp_Line0.source1
#print axioms AspisR1.JGp_Line0.source2
#print axioms AspisR1.JGp_Line1.source0
#print axioms AspisR1.JGp_Line1.source1
#print axioms AspisR1.JGp_Line1.source2
#print axioms AspisR1.JGp_Line2.source0
#print axioms AspisR1.JGp_Line2.source1
#print axioms AspisR1.JGp_Line2.source2
#print axioms AspisR1.JGp_Line3.source0
#print axioms AspisR1.JGp_Line3.source1
#print axioms AspisR1.JGp_Line3.source2
#print axioms AspisR1.JGp_Line4.source0
#print axioms AspisR1.JGp_Line4.source1
#print axioms AspisR1.JGp_Line4.source2
#print axioms AspisR1.JGp_Line5.source0
#print axioms AspisR1.JGp_Line5.source1
#print axioms AspisR1.JGp_Line5.source2
#print axioms AspisR1.JGp_Line6.source0
#print axioms AspisR1.JGp_Line6.source1
#print axioms AspisR1.JGp_Line6.source2
#print axioms AspisR1.JGp_Line7.source0
#print axioms AspisR1.JGp_Line7.source1
#print axioms AspisR1.JGp_Line7.source2
#print axioms AspisR1.JGp_Line8.source0
#print axioms AspisR1.JGp_Line8.source1
#print axioms AspisR1.JGp_Line8.source2
#print axioms AspisR1.JGp_Line9.source0
#print axioms AspisR1.JGp_Line9.source1
#print axioms AspisR1.JGp_Line9.source2
#print axioms AspisR1.JGp_Loop.source
#print axioms AspisR1.JGp_Opening0.length
#print axioms AspisR1.JGp_Opening0.source
#print axioms AspisR1.JGp_Opening1.length
#print axioms AspisR1.JGp_Opening1.source
#print axioms AspisR1.JGp_Opening2.length
#print axioms AspisR1.JGp_Opening2.source
#print axioms AspisR1.JGp_Opening3.length
#print axioms AspisR1.JGp_Opening3.source
#print axioms AspisR1.JGp_Opening4.length
#print axioms AspisR1.JGp_Opening4.source
#print axioms AspisR1.JGp_Opening5.length
#print axioms AspisR1.JGp_Opening5.source
#print axioms AspisR1.JGp_Opening6.length
#print axioms AspisR1.JGp_Opening6.source
#print axioms AspisR1.JGp_Opening7.length
#print axioms AspisR1.JGp_Opening7.source
#print axioms AspisR1.JGp_Opening8.length
#print axioms AspisR1.JGp_Opening8.source
#print axioms AspisR1.JGp_Opening9.length
#print axioms AspisR1.JGp_Opening9.source
#print axioms AspisR1.JGp_PreBatchFixture.inhabited
#print axioms AspisR1.JGp_Prepare.total
#print axioms AspisR1.JGp_Prepare.inhabited
#print axioms AspisR1.JGp_PrepareCuts.source
#print axioms AspisR1.FJp_Top.deployed
#print axioms AspisR1.JGp_PrepareLayout.logical
#print axioms AspisR1.JGp_PrepareLayout.y1
#print axioms AspisR1.JGp_PrepareLayout.semantic
#print axioms AspisR1.JGp_PrepareLayout.offsetY1
#print axioms AspisR1.JGp_PrepareLayout.inactive
#print axioms AspisR1.JGp_PrepareReads.semantic
#print axioms AspisR1.JGp_PrepareReads.y1
#print axioms AspisR1.JGp_PreparedQueries.source
#print axioms AspisR1.JGp_QueryCalls.source
#print axioms AspisR1.JGp_QueryNumeric.words_injective
#print axioms AspisR1.JGp_QueryNumeric.identified
#print axioms AspisR1.JGp_QueryNumeric.source
#print axioms AspisR1.JGp_Recombine.take
#print axioms AspisR1.JGp_Recombine.drop
#print axioms AspisR1.JGp_Recombine.length
#print axioms AspisR1.JGp_RecombinedReads.semantic
#print axioms AspisR1.JGp_RecombinedReads.y1
#print axioms AspisR1.JGp_Row0.node
#print axioms AspisR1.JGp_Row0.source
#print axioms AspisR1.JGp_Row0.regular
#print axioms AspisR1.JGp_Row1.node
#print axioms AspisR1.JGp_Row1.source
#print axioms AspisR1.JGp_Row1.regular
#print axioms AspisR1.JGp_Row2.node
#print axioms AspisR1.JGp_Row2.source
#print axioms AspisR1.JGp_Row2.regular
#print axioms AspisR1.JGp_Row3.node
#print axioms AspisR1.JGp_Row3.source
#print axioms AspisR1.JGp_Row3.regular
#print axioms AspisR1.JGp_Row4.node
#print axioms AspisR1.JGp_Row4.source
#print axioms AspisR1.JGp_Row4.regular
#print axioms AspisR1.JGp_Row5.node
#print axioms AspisR1.JGp_Row5.source
#print axioms AspisR1.JGp_Row5.regular
#print axioms AspisR1.JGp_Row6.node
#print axioms AspisR1.JGp_Row6.source
#print axioms AspisR1.JGp_Row6.regular
#print axioms AspisR1.JGp_Row7.node
#print axioms AspisR1.JGp_Row7.source
#print axioms AspisR1.JGp_Row7.regular
#print axioms AspisR1.JGp_Row8.node
#print axioms AspisR1.JGp_Row8.source
#print axioms AspisR1.JGp_Row8.regular
#print axioms AspisR1.JGp_Row9.node
#print axioms AspisR1.JGp_Row9.source
#print axioms AspisR1.JGp_Row9.regular
#print axioms AspisR1.JGp_Rows.source
#print axioms AspisR1.JGp_Rows.regular
#print axioms AspisR1.JGp_Rows.nonzero
#print axioms AspisR1.JGp_Rows.addresses
#print axioms AspisR1.JGp_Rows.fibres
#print axioms AspisR1.JGp_SemanticIdentity.source
#print axioms AspisR1.JGp_Shape.lengths
#print axioms AspisR1.JGp_Shape.step
#print axioms AspisR1.JGp_Shape.nonzero
#print axioms AspisR1.JGp_Shape.query
#print axioms AspisR1.JGp_Shape.row_eq
#print axioms AspisR1.JGp_Slot0.length
#print axioms AspisR1.JGp_Slot0.source
#print axioms AspisR1.JGp_Slot1.length
#print axioms AspisR1.JGp_Slot1.source
#print axioms AspisR1.JGp_Slot2.length
#print axioms AspisR1.JGp_Slot2.source
#print axioms AspisR1.JGp_TX1Geometry.inhabited
#print axioms AspisR1.JGp_TX1Initial.zeroCall
#print axioms AspisR1.JGp_TX1Initial.inhabited
#print axioms AspisR1.JGp_ValuesIdentity.source
#print AspisR1.JGp_PreBatchFixture.inhabited
#print AspisR1.JGp_PreBatchFixture.Remaining
#print AspisR1.JGp_BatchInput.source
#print AspisR1.FJp_Top.deployed
#print axioms AspisR1.FJp_Top.deployed
