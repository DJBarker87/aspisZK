import re,sys,subprocess
L=sys.argv[1]; D=sys.argv[2]
def frontier(m):
    return subprocess.check_output(['python3','-I','frontier.py',L,D,'--omit','OMIT_MODULES.txt',m],text=True).split('\t')[1].split()
def decl(m,name,kinds='def|abbrev|structure|theorem'):
    lines=open(f'{L}/{m}.lean').read().split('\n')
    s=next(i for i,l in enumerate(lines) if re.match(rf'^({kinds}) {re.escape(name)}\b',l))
    e=s+1
    while e<len(lines) and not re.match(r'^(def|abbrev|structure|theorem|lemma|/--|end |namespace|instance|@\[)',lines[e]): e+=1
    while e>s and lines[e-1].strip()=='' : e-=1
    return '\n'.join(lines[s:e])
def opens(m,drop):
    out=[]
    for l in open(f'{L}/{m}.lean'):
        if l.startswith('open '):
            toks=l.strip()
            for d in drop: toks=toks.replace(d,'')
            toks=re.sub(r'\s+',' ',toks).strip()
            if toks not in ('open','open ()'): out.append(toks)
    return out
hdr='set_option autoImplicit false\nnoncomputable section\n'
def write(name,imports,ns,opn,body,extra_imports=()):
    txt='\n'.join('import '+i for i in list(dict.fromkeys(list(extra_imports)+imports)))+'\n\n'+hdr+f'namespace {ns}\n'+'\n'.join(opn)+'\n\n'+body+'\n\nend '+ns+'\n'
    open(f'trimmed/{name}.lean','w').write(txt); print('wrote',name,len(imports),'imports')
# 1 SourceInputs
write('AspisLib_SourceInputs',frontier('R1FinalSoundness'),'AspisR1.R1FinalSoundness',
      opens('R1FinalSoundness',['DecoderInstanceBoundary']),decl('R1FinalSoundness','SourceInputs','structure'))
# 2 Recorded: dec, binaryCollision, SourceInputs
body='abbrev SourceInputs := R1FinalSoundness.SourceInputs\n\n'+decl('RecordedBinaryExperimentBin','dec')+'\n'+decl('RecordedBinaryExperimentBin','binaryCollision')
write('AspisLib_Recorded',frontier('RecordedBinaryExperimentBin'),'AspisR1.RecordedBinaryExperimentBin',
      opens('RecordedBinaryExperimentBin',['DecoderInstanceBoundaryBin']),body,['AspisLib_SourceInputs'])
# 3 Tag
write('AspisLib_Tag',frontier('InitialTagDecision'),'AspisR1.InitialTagDecision',
      opens('InitialTagDecision',['RecordedBinaryExperimentBin'])+['open AspisR1.RecordedBinaryExperimentBin'],
      decl('InitialTagDecision','erased_transcript_tag','theorem'),['AspisLib_Recorded'])
# 4 QueryAccounting
body='variable {X M C I A Y : Type} [DecidableEq I]\n\n'+decl('DecoderQueryAccounting','starts_le_queries','theorem')+'\n\n'+decl('DecoderQueryAccounting','AdversaryQueries')
write('AspisLib_QueryAccounting',frontier('DecoderQueryAccounting'),'AspisR1.DecoderQueryAccounting',
      opens('DecoderQueryAccounting',['RecordedBinaryExperimentBin'])+['open AspisR1.RecordedBinaryExperimentBin'],body,['AspisLib_Recorded'])
# 5 Guard
write('AspisLib_Guard',frontier('OraclePortAdmission'),'AspisR1.OraclePortAdmission',
      opens('OraclePortAdmission',['open RecordedBinaryExperimentBin (SourceInputs)'])+['open AspisR1.RecordedBinaryExperimentBin (SourceInputs)'],
      decl('OraclePortAdmission','Guard'),['AspisLib_Recorded'])
