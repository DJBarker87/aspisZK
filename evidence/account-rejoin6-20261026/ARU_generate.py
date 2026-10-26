from pathlib import Path
header='''set_option autoImplicit false
noncomputable section
namespace AspisR1.{ns}
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry S2W_D189Wrappers
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw SCE_Experiment S2W_NativeConsolidation
'''
params=''' {W A C Tx : Type} (L : Library W (Nat → Record))
    (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
    (allocator : Allocator A) (c : DrvC_Installation.Configuration FIo_Install.W C)
    (err : C) (r : NP6_StdModel.Reservation)
    (native1 : S2W_ExtractionBoundary.First) (native2 : S2W_ExtractionBoundary.Second)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (extraction : S2W_DigestExtraction.AeneasExtraction
      (DrvC_Installation.sdk (FIp_Install.configuration err c r)) native1 native2 hashv)
    (a : Adversary A) (H : Bytes → State)
    (n : ARU_Support.At (Tx := Tx) L copy allocator c err r native1 native2 hashv a H)'''
args='L copy allocator c err r native1 native2 hashv extraction a H n'
def write(ns,imports,body,thms):
 Path('lean/'+ns+'.lean').write_text(''.join('import '+i+'\n' for i in imports)+header.format(ns=ns)+body+'\n'+''.join('#print axioms '+t+'\n' for t in thms)+'end AspisR1.'+ns+'\nend\n')
write('ARU_Replies',['ARU_Support'], 'theorem accepted'+params+''' :
    (eval H (SCE_Execution.firstCode (FIp_Install.configuration err c r) hashv copy allocator
      CPH_Program.verifier (eval H a.first).2)).2 = ok (.Ok (n.entry.saved,n.entry.post1,n.entry.final1)) ∧
    (eval H (SCE_Execution.secondCode (FIp_Install.configuration err c r) hashv allocator
      CPH_Program.verifier (eval H (a.second (eval H a.first).2 n.entry.saved n.entry.post1 n.entry.final1)).2)).2 =
      ok (.Ok (n.entry.post2,n.entry.final2)) ∧
    accepted (eval H (account (FIp_Install.configuration err c r) hashv copy allocator CPH_Program.verifier a)).2 = true := by
  exact ARU_NativeReplies.accepted c err r hashv copy allocator native1 native2 extraction H a
    CPH_Program.verifier n.entry.saved n.entry.post1 n.entry.post2 n.entry.final1 n.entry.final2
    n.firstAgrees n.secondAgrees n.entry.accepted1 n.entry.accepted2
''',['accepted'])
write('ARU_Cuts',['ARU_Replies','SCH_SourceFirst','SCH_SourceSecond','SCH_DecodedCuts'], 'theorem selected'+params+''' :
    ∃ f s, SourceCuts (SCH_IdealSdk.dictionary (FIp_Install.configuration err c r) hashv H)
      (eval H a.first).2.entry.first
      ((eval H (a.second (eval H a.first).2 n.entry.saved n.entry.post1 n.entry.final1)).2.entry.second secondSizes)
      n.entry.saved f s ∧
      Port1_Driver.decodeSemantic (SCH_IdealSdk.dictionary (FIp_Install.configuration err c r) hashv H) f.pub =
        ok (some f.semantic) := by
  have replies := ARU_Replies.accepted '''+args+'''
  exact SCH_DecodedCuts.pair _ CPH_Program.verifier _ _ _ _ _ n.entry.saved
    (SCH_SourceFirst.accepted _ hashv copy allocator CPH_Program.verifier _ n.entry.saved n.entry.post1 n.entry.final1 H replies.1)
    (SCH_SourceSecond.accepted _ hashv allocator CPH_Program.verifier _ n.entry.post2 n.entry.final2 H replies.2.1)
''',['selected'])
write('ARU_Checkpoint',['ARU_Cuts','ARQ_BankCut'], 'theorem selected'+params+'''
    (std : S2W_TrustedStd.TrustedStd copy) :
    ∃ f s, SourceCuts (SCH_IdealSdk.dictionary (FIp_Install.configuration err c r) hashv H)
      (eval H a.first).2.entry.first
      ((eval H (a.second (eval H a.first).2 n.entry.saved n.entry.post1 n.entry.final1)).2.entry.second secondSizes)
      n.entry.saved f s ∧
      MultiproofConeCanonical.bytesOf s.checkpoint.val = MultiproofConeCanonical.bytesOf n.entry.saved.val := by
  obtain ⟨f,s,cuts,decoded⟩ := ARU_Cuts.selected '''+args+'''
  exact ⟨f,s,cuts,ARQ_BankCut.checkpoint c err r hashv copy std allocator native1 native2 extraction a H
    n.entry.saved n.entry.post1 n.entry.post2 n.entry.final1 n.entry.final2 n.entry.accepted1 n.entry.accepted2
    n.entry.p n.entry.t n.entry.u n.entry.actions n.entry.game n.entry.RuntimePersistence f s cuts⟩
''',['selected'])
