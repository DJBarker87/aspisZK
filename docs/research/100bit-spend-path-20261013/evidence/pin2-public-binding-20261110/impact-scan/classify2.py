import collections,re,json
CORE={'R0P.Core','PublicOptionShape','R1SemanticPublicWire','R1SemanticPublicWireRoundTrip','R1SemanticPublicWireInjective','R1SemanticPublicWireSound','R1SemanticPublicWireSurjective','R1SemanticPublicByteBinding','R1SemanticPublicCodecComplete','R1PublicByteCodec','R1PublicByteCodecLaws','PublicCodecAgreement','R1PublicCodecAgreement'}
def parent(n):
    n=re.sub(r'^_private\.[A-Za-z0-9_.]+?\.0\.','',n)
    parts=n.split('.')
    while len(parts)>1 and (re.match(r'^(match_\d+|_proof_\d+|proof_\d+|eq_\d+|eq_def|splitter|congr_simp|_unfold|_sunfold|induct|_simp_\d+|_cstage\d|_closed_\d+|_lambda_\d+|_spec_\d+|_auxLemma\d*|_flat_ctor|sizeOf_spec|injEq|inj|noConfusion)$',parts[-1]) or parts[-1].startswith('_')):
        parts.pop()
    return '.'.join(parts)
B={'R0P.Public.mk','R0P.Public.casesOn','R0P.Public.rec','R0P.Public.recOn','R0P.Public.noConfusion','R0P.Public.mk.injEq','R0P.Public.mk.inj','R0P.Public.ext','R0P.Public.ext_iff','R0P.Public.noConfusionType'}
W={'AspisR1.SemanticPublicWire.Common.mk','AspisR1.SemanticPublicWire.Common.casesOn','AspisR1.SemanticPublicWire.Common.rec','AspisR1.SemanticPublicWire.Common.recOn','AspisR1.SemanticPublicWire.Common.mk.injEq','AspisR1.SemanticPublicWire.Common.mk.inj','AspisR1.SemanticPublicWire.Common.noConfusion'}
P=re.compile(r'^AspisR1\.SemanticPublicWire\.(decodeAfter|decodeTransfer|decodeWithdrawal|decode|read\w+|afterBytes|header|encode|expect)(\.|$)|^AspisR1\.PublicOptionShape\.(canonical|check)(\.|$)|^AspisR1\.PublicByteCodec\.(publicCodec|fieldsCodec|toFields|fromFields|publicFieldsEquiv|Fields|WirePublic|encode|parseRaw)(\.|$)')
CHG=re.compile(r'^AspisR1\.(SemanticPublicWireRoundTrip\.encode_length|SemanticPublicByteBinding\.parsed_length|SemanticPublicCodecComplete\.(parsed_length_bound|parsed_init_fits|parsed_init_frame_length|parsed_length_u32)|PublicCodecAgreement\.(encode_none_iff|encode_exists_iff)|PublicOptionShape\.(private_transfer_updated_canonical|withdrawal_updated_canonical)|PublicByteCodec\.(encode_success_bound|roundtrip))$')
X=re.compile(r'^(FIq_Native|AspisR1PublicPreparation|AspisR1PublicSerializer)\S*(SemanticPublic|r0\.Public)(\.|$)|^AspisR1\.F3_Model\.SemanticPublic')
REAL_L={'NDO_JFp_InitBytes','NDO_JFp_SeedHash','NDO_JFp_SHADigest','NDO_JFs_ExactInitialization','NDO_JFs_ExactSerialization','NDO_JFs_PublicSerialization','NDO_JFs_SerializerSize','NDO_JFs_SerializerSource','NDO_JFu_OracleSeed','NDO_JFu_TranscriptLength','NDO_JFw_NativeRow18','NDO_JFw_Records','NDO_JFz_Parsed','NDO_JFz_Row17','NDO_JFz_Row18','NHG_Lengths','NHG_ProducerDomains','NHG_ProducerWidths','NHG_PublicCarrier','R1SelectedTranscriptParams','RPz7_F3J_Public','RPz8_F3V_Public','WireBindingRecordCodec'}
rel=set(open('release_closure.txt').read().split())
recs=collections.defaultdict(lambda: {'kind':set(),'cats':set()})
for l in open('scan6.tsv'):
    m,d,k,tr,tl,vr,vl=l.rstrip('\n').split('\t')
    allr=set(tr.split())|set(vr.split()); vrs=set(vr.split())
    r=recs[(m,parent(d))]; r['kind'].add(k)
    if allr & B: r['cats'].add('B')
    if allr & W: r['cats'].add('W')
    if any(P.match(x) for x in vrs): r['cats'].add('P')
    if any(CHG.match(x) for x in allr): r['cats'].add('U')
    if any(X.match(x) for x in allr): r['cats'].add('X')
    if any(x.startswith(('AspisR1.SemanticPublicWire.parsePublic','AspisR1.PublicOptionShape.canonical')) for x in tr.split()): r['cats'].add('S')
for l in open('scan7.tsv'):
    m,d,k,tr,tl,vr,vl=l.rstrip('\n').split('\t')
    if m in REAL_L: recs[(m,parent(d))]['cats'].add('L'); recs[(m,parent(d))]['kind'].add(k)
out=[(m,p,'/'.join(sorted(r['kind'])),sorted(r['cats'])) for (m,p),r in recs.items() if r['cats'] and m in rel]
json.dump(out,open('cls2.json','w'))
noncore=[o for o in out if o[0] not in CORE]
c=collections.Counter(); mods=collections.defaultdict(set)
for m,p,k,cats in noncore:
    for x in cats: c[x]+=1; mods[x].add(m)
print('noncore decls by cat',dict(c)); print('modules by cat',{k:len(v) for k,v in mods.items()})
need=[o for o in noncore if set(o[3])&{'B','W','P','U','L'}]
print('need-edit candidate decls (B/W/P/U/L):',len(need),'modules',len({o[0] for o in need}))
xonly=[o for o in noncore if 'X' in o[3] and not set(o[3])&{'B','W','P','U','L'}]
print('X-only decls',len(xonly),'modules',len({o[0] for o in xonly}))
json.dump(need,open('need.json','w')); json.dump(xonly,open('xonly.json','w'))
