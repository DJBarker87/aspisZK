from pathlib import Path
import re
R=Path(__file__).resolve().parents[2];L=R/'docs/research/100bit-spend-path-20261013/lean'
s=(L/'ChildJoin_Accepted.lean').read_text();header=s[:s.index('theorem accepted_run')].replace('import ChildJoin_Decoder','import ChildJoin_Decoder\nimport VTop_Checkpoint').replace('namespace AspisR1.ChildJoin_Accepted','namespace AspisR1.VTop_Accepted')
statement=s[s.index('theorem accepted_run'):s.index(' := by\n  obtain')]
statement=statement.replace('(ops : AdapterRw.Ops)', '(adapter : AdapterRw.Ops) (stage : VTop_Stages.Ops)')
statement=statement.replace('    (port : ChildConeJoin E ops)', '''    (reserved : Bool)
    (checkpointSource : VTop_Checkpoint.CheckpointSourceJoin stage
      (AdapterRw.SolanaDigest.Insts.Aspis_coreDigestDigest32 ops) () reserved)
    (checkpointOracle : CheckpointBytes5Inputs.Oracle
      (VTop_Checkpoint.digest (AdapterRw.SolanaDigest.Insts.Aspis_coreDigestDigest32 ops)) () H)
    (port : ChildConeJoin E ops)''')
old='''      CheckpointWriterConeJoin ops checkpointHeader H f.semantic f.pub f.proof f.split →
      CheckpointReaderConeJoin ops checkpointHeader H s.pub s.proof s.checkpoint →'''
assert old in statement
statement=statement.replace(old,'''      VTop_Checkpoint.WriterProvenance stage
        (AdapterRw.SolanaDigest.Insts.Aspis_coreDigestDigest32 ops) () f.semantic f.proof f.split →''')
statement=re.sub(r'\bops\b','(VTop_Entry.install adapter stage)',statement)
proof=''' := by
  obtain ⟨f,s,outer,pre,middle,fs,ss,cuts,expanded,owned,layout,unchanged,firstBefore,secondBefore,continuation⟩ :=
    ChildJoin_Accepted.accepted_run L sdk copy std allocator e1 e2 w1 w2 admission1 admission2
      (VTop_Entry.install adapter stage) native1 native2 hashv extraction sha256 H p1 syscall
      program data1 data2 slot state1 state2 final1 final2 saved post1 post2 accepted1 accepted2
      port firstMarks secondMarks
  refine ⟨f,s,outer,pre,middle,fs,ss,cuts,expanded,owned,layout,unchanged,firstBefore,secondBefore,?_⟩
  intro nodes y1 provenance history p2prime entry multiproof scan
  exact continuation nodes y1
    (VTop_Checkpoint.writer_join adapter stage H f.semantic f.pub f.proof f.split reserved
      checkpointSource checkpointOracle provenance)
    (VTop_Checkpoint.reader_join adapter stage H s.pub s.proof s.checkpoint reserved
      checkpointSource checkpointOracle)
    history p2prime entry multiproof scan

#print axioms accepted_run
#print accepted_run
end AspisR1.VTop_Accepted
end
'''
# The original theorem, as well as its imports and continuation, remains untouched.
header=header.replace('import S2W_D189Consolidation','import ChildJoin_Accepted')
(L/'VTop_Accepted.lean').write_text(header+statement+proof)
