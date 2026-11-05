from pathlib import Path
import hashlib,json
E=Path(__file__).resolve().parent;p=E.parent/'carriers-bind-20261105/NGS_PersistedCarriers.lean';s=p.read_text()
head=s[:s.index('/-- Direct NGR')].replace('import NGS_Carriers','import NHT_AuthAccepted\nimport NGS_PersistedCarriers').replace('namespace AspisR1.NGS_CARRIERS','namespace AspisR1.NHT_AuthCarriers')
a=s.index('theorem saved_to_carriers');b=s.index(' := by',a)
sig=s[a:b].replace('theorem saved_to_carriers','theorem authenticated_saved_to_carriers')
start=sig.index('    (readerResult :');stop=sig.index(' :\n    (bytesOf',start)
reader=sig[start:stop].replace('    (readerResult : ','').rstrip(')')
# same fixed input carriers and release None observer; stage2 slot association stays explicit
sig=sig[:start]+'''    (driverOps : VTop_Stages.Ops)
    (driverD : VTop_Stages.aspis_core.digest.Digest32 Unit)
    (stage2_owned : (ops).op11 (AdapterRw.SolanaDigest.Insts.Aspis_coreDigestDigest32 ops)
      s.pub s.proof s.checkpoint () none =
      NHT_EmittedAuth.tx2_authenticated (NHT_Tx2CommonModel.constants driverOps)
        driverD s.pub s.proof s.checkpoint () none)
    (driverAccepted : NHT_EmittedAuth.tx2_authenticated
      (NHT_Tx2CommonModel.constants driverOps) driverD s.pub s.proof s.checkpoint () none =
      ok (.Ok ()))'''+sig[stop:]
body=''' := by
  have readerResult := stage2_owned.trans driverAccepted
  exact NGS_CARRIERS.saved_to_carriers base err r hashv copy allocator a H
    Q bound reached prepared accumulator domain hp hu hc p t u n1 n2 actions std
    valid1 system data1 state1 final1 post1 game native_writer_result protection
    ordinary RuntimePersistence L sdk w2 related2 valid2 f s finish1 proof1Index
    public1Index proof1Read public1Read range1 length1 proof2Index proof2Read range2
    length2 v validation encoding writerResult checkpoint2Index checkpoint2Read readerResult
#print axioms authenticated_saved_to_carriers
end
end AspisR1.NHT_AuthCarriers
'''
(E/'NHT_AuthCarriers.lean').write_text(head+sig+body)
(E/'NHT_CARRIERS_PROVENANCE.json').write_text(json.dumps({'source':str(p),'sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'change':'Reuse full NGS/NGR composition; replace readerResult with SAME driver slot equation and acceptance. All source/account/history premises retained.'},indent=2)+'\n')
