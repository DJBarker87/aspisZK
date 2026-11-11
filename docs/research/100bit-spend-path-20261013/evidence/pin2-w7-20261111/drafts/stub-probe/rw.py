import re,sys
P=r'\((?:[^()]|\((?:[^()]|\((?:[^()]|\([^()]*\))*\))*\))*\)'
A=r'(?:'+P+r'|[^\s()=]+)'
rx=re.compile(r'(?:AspisR1PublicPreparation\.)?r1_semantic\.public_transcript\s+('+A+r')\s+('+A+r')\s+('+A+r')\s+('+A+r')\s*=\s*ok\s+\(\.Ok\s+('+A+r')\)')
def sub(m):
    d,p,h,r,t=m.groups()
    return ('AspisR1PublicPreparationPIN2.r1_semantic.public_transcript (AspisR1PublicPreparation.PIN2W7_TranscriptCopy.digest '+d+')\n'
            '        (AspisR1PublicPreparation.PreparationBinding.toPIN2 '+p+') '+h+' '+r+
            '=ok (.Ok (AspisR1PublicPreparation.PIN2W7_TranscriptCopy.transcript '+t+'))')
s=open(sys.argv[1]).read()
s2,n=rx.subn(sub,s)
open(sys.argv[2],'w').write(s2)
print(sys.argv[1].rsplit('/',1)[-1],'rewrites',n)
