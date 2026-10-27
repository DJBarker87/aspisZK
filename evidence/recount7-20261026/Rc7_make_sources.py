from pathlib import Path
R=Path(__file__).resolve().parents[2]; L=R/'lean'
s=(L/'P2P_R5Top.lean').read_text()
head=s[:s.index('theorem deployed')].replace('AspisR1.P2P_R5Top','AspisR1.Rc7_Native')
binders=s[s.index('theorem deployed'):s.index('    (D : LiteralByteProtocol.Decoder)')].replace('theorem deployed','theorem accepted')
result=s[s.index('    (P2P_R5Result.Outcome'):s.index('    ((∀ H : Bytes')].strip().removesuffix(' ∧')
body=s[s.index('  · obtain ⟨_,_,source,_,_⟩'):s.index('  · simpa only')]
body=body.replace('  · obtain','  obtain',1)
body='\n'.join(line[2:] if line.startswith('    ') else line for line in body.splitlines())
# keep block indentation at two spaces
body='\n'.join('  '+line if not line.startswith('  ') else line for line in body.splitlines())
# easier extract exact native branch with outer bullet removed only
body=s[s.index('  · obtain ⟨_,_,source,_,_⟩'):s.index('  · simpa only')]
body='\n'.join(('  '+line[4:] if line.startswith('    ') else line.replace('  · obtain','  obtain',1)) for line in body.splitlines())
(L/'Rc7_Native.lean').write_text(head+binders+' :\n    '+result+' := by\n'+body+'\n\n#print axioms accepted\nend AspisR1.Rc7_Native\nend\n')
# New top is FGl conclusion with a single native-selected recorder, and P2P result.
s=(L/'FGl_Headline.lean').read_text()
s='import Rc7_Native\nimport P2P_Release\nimport P2P_Accounting\n'+s
s=s.replace('AspisR1.FGl_Headline','AspisR1.Rc7_Top')
s=s.replace('    (select : F3X_Projection.Output → R9PoolRuntimeBinding.Inputs × R9PoolRuntimeBinding.Inputs) :', '''    :
    let select : F3X_Projection.Output → R9PoolRuntimeBinding.Inputs × R9PoolRuntimeBinding.Inputs :=
      fun _ => P2P_NativeSelection.pair
        (DrvC_Installation.sdk (Rc5_Install.configuration indexError c reservation))
        CPH_Program.verifier e1 e2 data2 slot;''')
s=s.replace('(Rc6_Result.Outcome','(P2P_Result.Outcome')
s=s.replace('      (p.physicalEvents t) hashv) ∧','''      (p.physicalEvents t) hashv
      (BinRawByteCollisionTargets.event SelectedTranscriptParams.params.iv (Q0+Q1+2965)
        (eval H (Hiq_RecordedJoint.program
          (F3X_Account.program (Rc5_Install.configuration indexError c reservation) hashv P)
          F3X_Projection.project select)))) ∧''')
s=s.replace(' := by\n  have prepare', ''' := by
  dsimp only
  let select : F3X_Projection.Output → R9PoolRuntimeBinding.Inputs × R9PoolRuntimeBinding.Inputs :=
    fun _ => P2P_NativeSelection.pair
      (DrvC_Installation.sdk (Rc5_Install.configuration indexError c reservation))
      CPH_Program.verifier e1 e2 data2 slot
  have prepare''',1)
a=s.index('  · obtain ⟨_,_,source,_,_⟩'); b=s.index('  · refine ⟨F3X_ModelClaims',a)
old=s[a:b]
old=old.replace('Rc5_Source.source','P2P_Source.source').replace('Rc5_Close.from_saf','P2P_R5Close.from_saf').replace('exact Rc6_Result.strengthen','have strengthened := P2P_R6Result.strengthen')
old+='''    exact P2P_Release.remove L e1 e2 w1 w2
      (Rc5_Install.configuration indexError c reservation).adapter
      (Rc5_Install.configuration indexError c reservation).currentBase
      (Rc5_Install.configuration indexError c reservation).reserved
      (Rc5_Install.configuration indexError c reservation).query
      (Rc5_Install.configuration indexError c reservation).geometry
      (Rc5_Install.configuration indexError c reservation).stageBase
      (Rc5_Install.configuration indexError c reservation).finish c.boundaries reservation
      CPH_Program.verifier data1 data2 slot saved post1 post2 H
      (DrvC_Implementation.driver (Rc5_Install.configuration indexError c reservation)) prior
      (p.physicalEvents t) hashv
      (F3X_Account.program (Rc5_Install.configuration indexError c reservation) hashv P)
      F3X_Projection.project (Q0+Q1)
      (F3Y_AccountMass.budget (Rc2_Install.configuration (Rc5_Install.seed indexError c) reservation)
        hashv D words P (Q0+Q1) queries) strengthened
'''
# actually use helper to avoid repeated source proof
start=old.index('    have strengthened :=')
old='''  · have original := Rc7_Native.accepted L sdk copy std allocator e1 e2 w1 w2
      admission1 admission2 c indexError reservation native1 native2 hashv extraction sha256 H p1 syscall
      data1 data2 slot state1 state2 final1 final2 saved post1 post2 accepted1 accepted2 root length
      prior words p t u actions game RuntimePersistence
'''+old[start:]
s=s[:a]+old+s[b:]
s=s.replace('/-- Current Rc5 native/history conclusions with the accepted raw join replaced\nby the SAME single charged account event. All selected preparation/query/geometry\nlaws are derived. Source-global finish laws and L159 remain explicit. -/', '/-- One native witness factory; one selected Q+2965 event for the frozen3\nheadline and P2Prime byte binding. Global finish owners and L159 remain. -/')
(L/'Rc7_Top.lean').write_text(s)
