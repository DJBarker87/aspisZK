import NDO_JGh_TX2_FrontierHeight17
import NDO_JGh_TX2_M1Root
import NDO_JGf_TX2_M0Root
import NDO_JGf_TX2_Sort
import NDO_JFn_Resume
import NDO_JGc_TX2_Obstruction70
import NDO_JGe_JoinedFixture
import RPz8_Rc10_Top
import NDO_JGh_TX2_M0LeafSources10
import NDO_JGh_TX2_M0LeafSources12
import NDO_JGh_TX2_M0LeafSources14
import NDO_JGh_TX2_M0LeafSources16
import NDO_JGh_TX2_M0LeafSources18
import NDO_JGh_TX2_M0LeafSources20
import NDO_JGh_TX2_M1LeafSources10
import NDO_JGh_TX2_M1LeafSources12
import NDO_JGh_TX2_M1LeafSources14
import NDO_JGh_TX2_M1LeafSources16
import NDO_JGh_TX2_M1LeafSources18
import NDO_JGh_TX2_M1LeafSources20

set_option autoImplicit false
noncomputable section
namespace AspisR1.JGh_TX2_CountFrontier
open OraclePortSelectedDraft
theorem length0 : JGh_TX2_Frontiers.coords0_185.length=163 := by
  simp only [JGh_TX2_Frontiers.coords0_000,JGh_TX2_Frontiers.coords0_001,JGh_TX2_Frontiers.coords0_002,JGh_TX2_Frontiers.coords0_003,JGh_TX2_Frontiers.coords0_004,JGh_TX2_Frontiers.coords0_005,JGh_TX2_Frontiers.coords0_006,JGh_TX2_Frontiers.coords0_007,JGh_TX2_Frontiers.coords0_008,JGh_TX2_Frontiers.coords0_009,JGh_TX2_Frontiers.coords0_010,JGh_TX2_Frontiers.coords0_011,JGh_TX2_Frontiers.coords0_012,JGh_TX2_Frontiers.coords0_013,JGh_TX2_Frontiers.coords0_014,JGh_TX2_Frontiers.coords0_015,JGh_TX2_Frontiers.coords0_016,JGh_TX2_Frontiers.coords0_017,JGh_TX2_Frontiers.coords0_018,JGh_TX2_Frontiers.coords0_019,JGh_TX2_Frontiers.coords0_020,JGh_TX2_Frontiers.coords0_021,JGh_TX2_Frontiers.coords0_022,JGh_TX2_Frontiers.coords0_023,JGh_TX2_Frontiers.coords0_024,JGh_TX2_Frontiers.coords0_025,JGh_TX2_Frontiers.coords0_026,JGh_TX2_Frontiers.coords0_027,JGh_TX2_Frontiers.coords0_028,JGh_TX2_Frontiers.coords0_029,JGh_TX2_Frontiers.coords0_030,JGh_TX2_Frontiers.coords0_031,JGh_TX2_Frontiers.coords0_032,JGh_TX2_Frontiers.coords0_033,JGh_TX2_Frontiers.coords0_034,JGh_TX2_Frontiers.coords0_035,JGh_TX2_Frontiers.coords0_036,JGh_TX2_Frontiers.coords0_037,JGh_TX2_Frontiers.coords0_038,JGh_TX2_Frontiers.coords0_039,JGh_TX2_Frontiers.coords0_040,JGh_TX2_Frontiers.coords0_041,JGh_TX2_Frontiers.coords0_042,JGh_TX2_Frontiers.coords0_043,JGh_TX2_Frontiers.coords0_044,JGh_TX2_Frontiers.coords0_045,JGh_TX2_Frontiers.coords0_046,JGh_TX2_Frontiers.coords0_047,JGh_TX2_Frontiers.coords0_048,JGh_TX2_Frontiers.coords0_049,JGh_TX2_Frontiers.coords0_050,JGh_TX2_Frontiers.coords0_051,JGh_TX2_Frontiers.coords0_052,JGh_TX2_Frontiers.coords0_053,JGh_TX2_Frontiers.coords0_054,JGh_TX2_Frontiers.coords0_055,JGh_TX2_Frontiers.coords0_056,JGh_TX2_Frontiers.coords0_057,JGh_TX2_Frontiers.coords0_058,JGh_TX2_Frontiers.coords0_059,JGh_TX2_Frontiers.coords0_060,JGh_TX2_Frontiers.coords0_061,JGh_TX2_Frontiers.coords0_062,JGh_TX2_Frontiers.coords0_063,JGh_TX2_Frontiers.coords0_064,JGh_TX2_Frontiers.coords0_065,JGh_TX2_Frontiers.coords0_066,JGh_TX2_Frontiers.coords0_067,JGh_TX2_Frontiers.coords0_068,JGh_TX2_Frontiers.coords0_069,JGh_TX2_Frontiers.coords0_070,JGh_TX2_Frontiers.coords0_071,JGh_TX2_Frontiers.coords0_072,JGh_TX2_Frontiers.coords0_073,JGh_TX2_Frontiers.coords0_074,JGh_TX2_Frontiers.coords0_075,JGh_TX2_Frontiers.coords0_076,JGh_TX2_Frontiers.coords0_077,JGh_TX2_Frontiers.coords0_078,JGh_TX2_Frontiers.coords0_079,JGh_TX2_Frontiers.coords0_080,JGh_TX2_Frontiers.coords0_081,JGh_TX2_Frontiers.coords0_082,JGh_TX2_Frontiers.coords0_083,JGh_TX2_Frontiers.coords0_084,JGh_TX2_Frontiers.coords0_085,JGh_TX2_Frontiers.coords0_086,JGh_TX2_Frontiers.coords0_087,JGh_TX2_Frontiers.coords0_088,JGh_TX2_Frontiers.coords0_089,JGh_TX2_Frontiers.coords0_090,JGh_TX2_Frontiers.coords0_091,JGh_TX2_Frontiers.coords0_092,JGh_TX2_Frontiers.coords0_093,JGh_TX2_Frontiers.coords0_094,JGh_TX2_Frontiers.coords0_095,JGh_TX2_Frontiers.coords0_096,JGh_TX2_Frontiers.coords0_097,JGh_TX2_Frontiers.coords0_098,JGh_TX2_Frontiers.coords0_099,JGh_TX2_Frontiers.coords0_100,JGh_TX2_Frontiers.coords0_101,JGh_TX2_Frontiers.coords0_102,JGh_TX2_Frontiers.coords0_103,JGh_TX2_Frontiers.coords0_104,JGh_TX2_Frontiers.coords0_105,JGh_TX2_Frontiers.coords0_106,JGh_TX2_Frontiers.coords0_107,JGh_TX2_Frontiers.coords0_108,JGh_TX2_Frontiers.coords0_109,JGh_TX2_Frontiers.coords0_110,JGh_TX2_Frontiers.coords0_111,JGh_TX2_Frontiers.coords0_112,JGh_TX2_Frontiers.coords0_113,JGh_TX2_Frontiers.coords0_114,JGh_TX2_Frontiers.coords0_115,JGh_TX2_Frontiers.coords0_116,JGh_TX2_Frontiers.coords0_117,JGh_TX2_Frontiers.coords0_118,JGh_TX2_Frontiers.coords0_119,JGh_TX2_Frontiers.coords0_120,JGh_TX2_Frontiers.coords0_121,JGh_TX2_Frontiers.coords0_122,JGh_TX2_Frontiers.coords0_123,JGh_TX2_Frontiers.coords0_124,JGh_TX2_Frontiers.coords0_125,JGh_TX2_Frontiers.coords0_126,JGh_TX2_Frontiers.coords0_127,JGh_TX2_Frontiers.coords0_128,JGh_TX2_Frontiers.coords0_129,JGh_TX2_Frontiers.coords0_130,JGh_TX2_Frontiers.coords0_131,JGh_TX2_Frontiers.coords0_132,JGh_TX2_Frontiers.coords0_133,JGh_TX2_Frontiers.coords0_134,JGh_TX2_Frontiers.coords0_135,JGh_TX2_Frontiers.coords0_136,JGh_TX2_Frontiers.coords0_137,JGh_TX2_Frontiers.coords0_138,JGh_TX2_Frontiers.coords0_139,JGh_TX2_Frontiers.coords0_140,JGh_TX2_Frontiers.coords0_141,JGh_TX2_Frontiers.coords0_142,JGh_TX2_Frontiers.coords0_143,JGh_TX2_Frontiers.coords0_144,JGh_TX2_Frontiers.coords0_145,JGh_TX2_Frontiers.coords0_146,JGh_TX2_Frontiers.coords0_147,JGh_TX2_Frontiers.coords0_148,JGh_TX2_Frontiers.coords0_149,JGh_TX2_Frontiers.coords0_150,JGh_TX2_Frontiers.coords0_151,JGh_TX2_Frontiers.coords0_152,JGh_TX2_Frontiers.coords0_153,JGh_TX2_Frontiers.coords0_154,JGh_TX2_Frontiers.coords0_155,JGh_TX2_Frontiers.coords0_156,JGh_TX2_Frontiers.coords0_157,JGh_TX2_Frontiers.coords0_158,JGh_TX2_Frontiers.coords0_159,JGh_TX2_Frontiers.coords0_160,JGh_TX2_Frontiers.coords0_161,JGh_TX2_Frontiers.coords0_162,JGh_TX2_Frontiers.coords0_163,JGh_TX2_Frontiers.coords0_164,JGh_TX2_Frontiers.coords0_165,JGh_TX2_Frontiers.coords0_166,JGh_TX2_Frontiers.coords0_167,JGh_TX2_Frontiers.coords0_168,JGh_TX2_Frontiers.coords0_169,JGh_TX2_Frontiers.coords0_170,JGh_TX2_Frontiers.coords0_171,JGh_TX2_Frontiers.coords0_172,JGh_TX2_Frontiers.coords0_173,JGh_TX2_Frontiers.coords0_174,JGh_TX2_Frontiers.coords0_175,JGh_TX2_Frontiers.coords0_176,JGh_TX2_Frontiers.coords0_177,JGh_TX2_Frontiers.coords0_178,JGh_TX2_Frontiers.coords0_179,JGh_TX2_Frontiers.coords0_180,JGh_TX2_Frontiers.coords0_181,JGh_TX2_Frontiers.coords0_182,JGh_TX2_Frontiers.coords0_183,JGh_TX2_Frontiers.coords0_184,JGh_TX2_Frontiers.coords0_185,List.length_append,List.length_cons,List.length_nil,Nat.reduceAdd]
#print axioms length0
theorem source0 : MultiproofConeCountLevels.sourceCount 18 JGf_TX2_Count0.indices00=
    (OraclePortSelectedDraft.orderedFrontier JGf_TX2_M0Roots.indices).length := by
  rw [JGf_TX2_Count0.total00,OraclePortSelectedDraft.orderedFrontier,List.length_mergeSort,
    JGh_TX2_Frontiers.front0_185]
  exact length0.symm
#print axioms source0
theorem length2 : JGh_TX2_Frontiers.coords2_163.length=141 := by
  simp only [JGh_TX2_Frontiers.coords2_000,JGh_TX2_Frontiers.coords2_001,JGh_TX2_Frontiers.coords2_002,JGh_TX2_Frontiers.coords2_003,JGh_TX2_Frontiers.coords2_004,JGh_TX2_Frontiers.coords2_005,JGh_TX2_Frontiers.coords2_006,JGh_TX2_Frontiers.coords2_007,JGh_TX2_Frontiers.coords2_008,JGh_TX2_Frontiers.coords2_009,JGh_TX2_Frontiers.coords2_010,JGh_TX2_Frontiers.coords2_011,JGh_TX2_Frontiers.coords2_012,JGh_TX2_Frontiers.coords2_013,JGh_TX2_Frontiers.coords2_014,JGh_TX2_Frontiers.coords2_015,JGh_TX2_Frontiers.coords2_016,JGh_TX2_Frontiers.coords2_017,JGh_TX2_Frontiers.coords2_018,JGh_TX2_Frontiers.coords2_019,JGh_TX2_Frontiers.coords2_020,JGh_TX2_Frontiers.coords2_021,JGh_TX2_Frontiers.coords2_022,JGh_TX2_Frontiers.coords2_023,JGh_TX2_Frontiers.coords2_024,JGh_TX2_Frontiers.coords2_025,JGh_TX2_Frontiers.coords2_026,JGh_TX2_Frontiers.coords2_027,JGh_TX2_Frontiers.coords2_028,JGh_TX2_Frontiers.coords2_029,JGh_TX2_Frontiers.coords2_030,JGh_TX2_Frontiers.coords2_031,JGh_TX2_Frontiers.coords2_032,JGh_TX2_Frontiers.coords2_033,JGh_TX2_Frontiers.coords2_034,JGh_TX2_Frontiers.coords2_035,JGh_TX2_Frontiers.coords2_036,JGh_TX2_Frontiers.coords2_037,JGh_TX2_Frontiers.coords2_038,JGh_TX2_Frontiers.coords2_039,JGh_TX2_Frontiers.coords2_040,JGh_TX2_Frontiers.coords2_041,JGh_TX2_Frontiers.coords2_042,JGh_TX2_Frontiers.coords2_043,JGh_TX2_Frontiers.coords2_044,JGh_TX2_Frontiers.coords2_045,JGh_TX2_Frontiers.coords2_046,JGh_TX2_Frontiers.coords2_047,JGh_TX2_Frontiers.coords2_048,JGh_TX2_Frontiers.coords2_049,JGh_TX2_Frontiers.coords2_050,JGh_TX2_Frontiers.coords2_051,JGh_TX2_Frontiers.coords2_052,JGh_TX2_Frontiers.coords2_053,JGh_TX2_Frontiers.coords2_054,JGh_TX2_Frontiers.coords2_055,JGh_TX2_Frontiers.coords2_056,JGh_TX2_Frontiers.coords2_057,JGh_TX2_Frontiers.coords2_058,JGh_TX2_Frontiers.coords2_059,JGh_TX2_Frontiers.coords2_060,JGh_TX2_Frontiers.coords2_061,JGh_TX2_Frontiers.coords2_062,JGh_TX2_Frontiers.coords2_063,JGh_TX2_Frontiers.coords2_064,JGh_TX2_Frontiers.coords2_065,JGh_TX2_Frontiers.coords2_066,JGh_TX2_Frontiers.coords2_067,JGh_TX2_Frontiers.coords2_068,JGh_TX2_Frontiers.coords2_069,JGh_TX2_Frontiers.coords2_070,JGh_TX2_Frontiers.coords2_071,JGh_TX2_Frontiers.coords2_072,JGh_TX2_Frontiers.coords2_073,JGh_TX2_Frontiers.coords2_074,JGh_TX2_Frontiers.coords2_075,JGh_TX2_Frontiers.coords2_076,JGh_TX2_Frontiers.coords2_077,JGh_TX2_Frontiers.coords2_078,JGh_TX2_Frontiers.coords2_079,JGh_TX2_Frontiers.coords2_080,JGh_TX2_Frontiers.coords2_081,JGh_TX2_Frontiers.coords2_082,JGh_TX2_Frontiers.coords2_083,JGh_TX2_Frontiers.coords2_084,JGh_TX2_Frontiers.coords2_085,JGh_TX2_Frontiers.coords2_086,JGh_TX2_Frontiers.coords2_087,JGh_TX2_Frontiers.coords2_088,JGh_TX2_Frontiers.coords2_089,JGh_TX2_Frontiers.coords2_090,JGh_TX2_Frontiers.coords2_091,JGh_TX2_Frontiers.coords2_092,JGh_TX2_Frontiers.coords2_093,JGh_TX2_Frontiers.coords2_094,JGh_TX2_Frontiers.coords2_095,JGh_TX2_Frontiers.coords2_096,JGh_TX2_Frontiers.coords2_097,JGh_TX2_Frontiers.coords2_098,JGh_TX2_Frontiers.coords2_099,JGh_TX2_Frontiers.coords2_100,JGh_TX2_Frontiers.coords2_101,JGh_TX2_Frontiers.coords2_102,JGh_TX2_Frontiers.coords2_103,JGh_TX2_Frontiers.coords2_104,JGh_TX2_Frontiers.coords2_105,JGh_TX2_Frontiers.coords2_106,JGh_TX2_Frontiers.coords2_107,JGh_TX2_Frontiers.coords2_108,JGh_TX2_Frontiers.coords2_109,JGh_TX2_Frontiers.coords2_110,JGh_TX2_Frontiers.coords2_111,JGh_TX2_Frontiers.coords2_112,JGh_TX2_Frontiers.coords2_113,JGh_TX2_Frontiers.coords2_114,JGh_TX2_Frontiers.coords2_115,JGh_TX2_Frontiers.coords2_116,JGh_TX2_Frontiers.coords2_117,JGh_TX2_Frontiers.coords2_118,JGh_TX2_Frontiers.coords2_119,JGh_TX2_Frontiers.coords2_120,JGh_TX2_Frontiers.coords2_121,JGh_TX2_Frontiers.coords2_122,JGh_TX2_Frontiers.coords2_123,JGh_TX2_Frontiers.coords2_124,JGh_TX2_Frontiers.coords2_125,JGh_TX2_Frontiers.coords2_126,JGh_TX2_Frontiers.coords2_127,JGh_TX2_Frontiers.coords2_128,JGh_TX2_Frontiers.coords2_129,JGh_TX2_Frontiers.coords2_130,JGh_TX2_Frontiers.coords2_131,JGh_TX2_Frontiers.coords2_132,JGh_TX2_Frontiers.coords2_133,JGh_TX2_Frontiers.coords2_134,JGh_TX2_Frontiers.coords2_135,JGh_TX2_Frontiers.coords2_136,JGh_TX2_Frontiers.coords2_137,JGh_TX2_Frontiers.coords2_138,JGh_TX2_Frontiers.coords2_139,JGh_TX2_Frontiers.coords2_140,JGh_TX2_Frontiers.coords2_141,JGh_TX2_Frontiers.coords2_142,JGh_TX2_Frontiers.coords2_143,JGh_TX2_Frontiers.coords2_144,JGh_TX2_Frontiers.coords2_145,JGh_TX2_Frontiers.coords2_146,JGh_TX2_Frontiers.coords2_147,JGh_TX2_Frontiers.coords2_148,JGh_TX2_Frontiers.coords2_149,JGh_TX2_Frontiers.coords2_150,JGh_TX2_Frontiers.coords2_151,JGh_TX2_Frontiers.coords2_152,JGh_TX2_Frontiers.coords2_153,JGh_TX2_Frontiers.coords2_154,JGh_TX2_Frontiers.coords2_155,JGh_TX2_Frontiers.coords2_156,JGh_TX2_Frontiers.coords2_157,JGh_TX2_Frontiers.coords2_158,JGh_TX2_Frontiers.coords2_159,JGh_TX2_Frontiers.coords2_160,JGh_TX2_Frontiers.coords2_161,JGh_TX2_Frontiers.coords2_162,JGh_TX2_Frontiers.coords2_163,List.length_append,List.length_cons,List.length_nil,Nat.reduceAdd]
#print axioms length2
theorem source2 : MultiproofConeCountLevels.sourceCount 18 JGf_TX2_Count2.indices00=
    (OraclePortSelectedDraft.orderedFrontier JGc_TX2_M2Roots.indices).length := by
  rw [JGf_TX2_Count2.total00,OraclePortSelectedDraft.orderedFrontier,List.length_mergeSort,
    JGh_TX2_Frontiers.front2_163]
  exact length2.symm
#print axioms source2
end AspisR1.JGh_TX2_CountFrontier
end
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGh_TX2_FinalFacts
open Aeneas Aeneas.Std Result
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep

def q := Port4B_KeyInstall.queries JFo_Prepared.value.queries

theorem keys (kind : Nat) : ∃ out : Array U64 16#usize,
    Port4B_Install.leaves.op5 (JGf_TX2_Keys.raw kind) 12#usize=ok out ∧
    Port4B_LeafLoop.KeyStream q 1 kind out 0#usize
      (OraclePortFrozenOrder.sortedPositions q 1 kind) := by
  obtain ⟨out,run,_front,_suffix⟩ := JGf_TX2_Sort.source kind
  refine ⟨out,run,?_⟩
  exact (Port4B_SortInstall.key_stream Port4B_Install.leaves q 1 kind
    (JGf_TX2_Keys.raw kind) out 12#usize (by decide) (by decide)
    (JGf_TX2_Keys.prefix_keys kind) run).2
#print axioms keys

theorem on_saved (saved : alloc.vec.Vec U8) (same : saved.val=JFx_NativeBytes.checkpoint.val)
    {Hash : Type} (D : VTop_Stages.aspis_core.digest.Digest32 Hash) (hash : Hash)
    (realizes : JFn_HashBoundary.Realizes JFp_SHADigest.digest) :
    Port4A_ReaderInstall.reader true (JFn_HashBoundary.dictionary JFp_SHADigest.digest D)
      (⟨saved.val,saved.property⟩ : Slice U8) JFx_NativeBytes.proof JFx_NativeBytes.publicInput .S2 hash=
        ok (.Ok (JFo_Prepared.value,JFo_Prepared.accumulator)) ∧
    (∃ (f : Nat → Bytes) (g : Nat → Nat → State),
      JGh_TX2_M1Roots.InputLaw f ∧ JGh_TX2_M1Roots.SiblingLaw g ∧
      OracleDecisionMultiTree.root JFp_SHADigest.digest
        (OracleDecisionMultiBuild.build JGh_TX2_M1Roots.indices f g 18 0)=JGh_TX2_M1Root.retainedRoot) ∧
    MultiproofConeCountLevels.sourceCount 18 JGf_TX2_Count0.indices00=
      (OraclePortSelectedDraft.orderedFrontier JGf_TX2_M0Roots.indices).length ∧
    MultiproofConeCountLevels.sourceCount 18 JGf_TX2_Count2.indices00=
      (OraclePortSelectedDraft.orderedFrontier JGc_TX2_M2Roots.indices).length ∧
    Port4B_Install.leaves.op3 JFx_NativeBytes.proof 3#usize=ok JGh_TX2_NodeViews.nodes0 ∧
    Port4B_Install.leaves.op3 JFx_NativeBytes.proof 4#usize=ok JGh_TX2_NodeViews.nodes1 ∧
    Port4B_Install.leaves.op3 JFx_NativeBytes.proof 5#usize=ok JGh_TX2_NodeViews.nodes2 :=
  ⟨JFn_Resume.on_saved saved same JFp_SHADigest.digest D hash realizes,JGh_TX2_M1Root.inhabited,
    JGh_TX2_CountFrontier.source0,JGh_TX2_CountFrontier.source2,
    JGh_TX2_NodeViews.source0,JGh_TX2_NodeViews.source1,JGh_TX2_NodeViews.source2⟩
#print axioms on_saved
end AspisR1.JGh_TX2_FinalFacts
end
#print AspisR1.JGc_TX2_Obstruction70.BatchGoal
#print AspisR1.JFn_HashBoundary.Realizes
#print AspisR1.JGe_TerminalCondition.Identified
#print axioms AspisR1.JGh_TX2_M1Root.source
#print axioms AspisR1.JGh_TX2_M1Root.inhabited
#print axioms AspisR1.JGh_TX2_M1Root.saved_root
#print axioms AspisR1.JGh_TX2_NodeViews.source0
#print axioms AspisR1.JGh_TX2_NodeViews.source1
#print axioms AspisR1.JGh_TX2_NodeViews.source2
#print axioms AspisR1.JGe_JoinedFixture.inhabited
#print axioms AspisR1.Rc10_Top.deployed
#check @AspisR1.JGh_TX2_FinalFacts.on_saved
#check @AspisR1.JGe_JoinedFixture.inhabited
#check @AspisR1.Rc10_Top.deployed
#print axioms AspisR1.JGh_TX2_M0Leaf10.source
#print axioms AspisR1.JGh_TX2_M0Leaf11.source
#print axioms AspisR1.JGh_TX2_M0Leaf12.source
#print axioms AspisR1.JGh_TX2_M0Leaf13.source
#print axioms AspisR1.JGh_TX2_M0Leaf14.source
#print axioms AspisR1.JGh_TX2_M0Leaf15.source
#print axioms AspisR1.JGh_TX2_M0Leaf16.source
#print axioms AspisR1.JGh_TX2_M0Leaf17.source
#print axioms AspisR1.JGh_TX2_M0Leaf18.source
#print axioms AspisR1.JGh_TX2_M0Leaf19.source
#print axioms AspisR1.JGh_TX2_M0Leaf20.source
#print axioms AspisR1.JGh_TX2_M0Leaf21.source
#print axioms AspisR1.JGh_TX2_M1Leaf10.source
#print axioms AspisR1.JGh_TX2_M1Leaf11.source
#print axioms AspisR1.JGh_TX2_M1Leaf12.source
#print axioms AspisR1.JGh_TX2_M1Leaf13.source
#print axioms AspisR1.JGh_TX2_M1Leaf14.source
#print axioms AspisR1.JGh_TX2_M1Leaf15.source
#print axioms AspisR1.JGh_TX2_M1Leaf16.source
#print axioms AspisR1.JGh_TX2_M1Leaf17.source
#print axioms AspisR1.JGh_TX2_M1Leaf18.source
#print axioms AspisR1.JGh_TX2_M1Leaf19.source
#print axioms AspisR1.JGh_TX2_M1Leaf20.source
#print axioms AspisR1.JGh_TX2_M1Leaf21.source
