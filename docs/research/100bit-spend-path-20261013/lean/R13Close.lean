import R13CloseSort
import R13CloseDedup
import R13CloseLevelRun
import R13ClosePaddingTail
import R13MultiproofReadSet
import QvStage2Privacy

/-! Focused coexistence/type audit of this source packet and its actual model
consumers. There is deliberately no new accepted-tx2 theorem: the eighteen
level schedule and global call correspondence are not yet proved. -/
#check AspisR1Stage2.R13Close.Sort.sort_prefix
#check AspisR1Stage2.R13Close.Dedup.dedup_step_pairs
#check AspisR1Stage2.R13Close.Level.binary_loop_write_fold
#check AspisR1Stage2.R13Close.Padding.source_chunks_cover
#check AspisR1Stage2.R13Close.Padding.source_tail_mod
#check AspisR1Stage2.R13Close.Padding.source_prefix_exact
#check AspisR1.BinBatchDedup.dedup_sound
#check AspisR1.BinBatchDedup.accepted_original_queries
#check AspisR1.BinMultiproof.Level
#check AspisR1.BinMultiproof.Accept
#check AspisR1.BinMultiproof.PaddedAccept
#check AspisR1.R13MultiproofReadSet.accepted_family
#check AspisR1.QvStage2.RetainedPrivacy.batchReadSet
#check AspisR1.QvStage2.stage2Budget_twelve
