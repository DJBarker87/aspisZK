import sys
d=sys.argv[1]
L=open(d+'/AspisRowStarts.lean').read().split('\n')
# 1-based line numbers from the source at a48bc69af17
hdr=L[0:27]          # lines 1..27 : imports, doc, options, namespace, opens, attribute, blank
body_i_a=L[27:203]   # lines 28..203 : caps ... rowCharge + blank
ii_a=L[203:305]      # lines 204..305: ite_le .. rows_weight + blank
vc=L[305:308]        # lines 306..308: verifierCharge doc, def, blank
ii_b=L[308:318]      # lines 309..318: verifier_weight + blank
i_b=L[318:333]       # lines 319..333: sum_indicator26, verifierCharge_eq + blank
ax=L[333:339]        # lines 334..339
tail=L[339:]         # end lines
assert hdr[2]=='import BinHonestQueryBudget' and hdr[25].startswith('attribute') and hdr[26]=='', hdr
assert ii_a[0].startswith('private theorem ite_le'), ii_a[0]
assert vc[1].startswith('def verifierCharge'), vc[1]
assert ii_b[1].startswith('theorem verifier_weight'), ii_b[1]
assert i_b[0].startswith('private theorem sum_indicator26'), i_b[0]
assert ax[0]=='#print axioms wt_absorb' and ax[5]=='#print axioms verifierCharge_eq', ax
assert tail[0]=='end AspisPerStep.RowStarts', tail
# (i)
h=list(hdr)
h[2]='import BinHonestStartFrames'
i21=h.index('open RecordedBinaryExperimentBin RawCutProverCompiler DecodedFirstReadUnionBound')
h[i21]='open RawCutProverCompiler DecodedFirstReadUnionBound'
i22=h.index('open BinHonestStartFrames BinHonestQueryBudget')
h[i22]='open BinHonestStartFrames'
iend=h.index('not determined here). -/')
h[iend]='not determined here).\n\nThe sampler-row theorems about R1\'s 33-row decoder (`sampler_weight`,\n`row_weight`, `rows_weight`, `verifier_weight`) are in `AspisRowStarts33`,\nin this namespace. -/'
out_i=h+body_i_a+vc+i_b+['#print axioms wt_absorb','#print axioms wt_init','#print axioms verifierCharge_eq']+tail
open(d+'/AspisRowStarts.lean','w').write('\n'.join(out_i))
# (ii)
h2=list(hdr)
h2[0:3]=['import AspisRowStarts','import BinHonestQueryBudget']
ie=h2.index('/-! Per-step accounting, piece (c), verifier part: the weighted count of the')
# keep original doc, add a first line
h2[ie]='/-! Split from `AspisRowStarts` (text unchanged): the 33-row theorems about R1\'s\ndecoder, used only by `AspisChargedWeight`, `AspisChargedHitMass` and\n`AspisChargedHitMassCheck`, not by the 40-row chain.\n\nPer-step accounting, piece (c), verifier part: the weighted count of the'
out_ii=h2+ii_a+ii_b+['#print axioms sampler_weight','#print axioms rows_weight','#print axioms verifier_weight']+tail
open(d+'/AspisRowStarts33.lean','w').write('\n'.join(out_ii))
