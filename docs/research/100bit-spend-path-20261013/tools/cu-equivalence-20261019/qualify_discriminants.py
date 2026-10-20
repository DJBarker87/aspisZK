"""Replace Aeneas's globally named discriminant registrations, invertibly.

Constructor declarations/order and ordinal mapping are unchanged. Only generated
registration names are qualified, so independently emitted modules can coexist.
"""
import re

def qualify(raw:bytes,namespace:str)->bytes:
    text=raw.decode();pattern=re.compile(r'@\[discriminant isize\]\n(inductive ([A-Za-z0-9_.]+) where\n.*?)(?=\n/--|\nend )',re.S)
    replacements=[]
    def sub(match):
        block,enum=match.group(1),match.group(2)
        constructors=re.findall(r'^\| ([A-Za-z0-9_]+)\s*:\s*(.*?)(?=^\| |\Z)',block,re.S|re.M)
        assert constructors,(namespace,enum)
        cases=[]
        for i,(name,typ) in enumerate(constructors):
            parts=[x.strip() for x in typ.strip().split('→')];assert parts[-1]==enum,(enum,name,typ)
            assert all('→' not in p and '(' not in p and ')' not in p for p in parts[:-1]),(enum,name,'unsupported constructor shape')
            cases.append('  | .'+name+' _'*(len(parts)-1)+' => '+str(i)+'#isize\n')
        registration='\ndef '+enum+'.read_discriminant : '+enum+' → Isize\n'+''.join(cases)
        registration+='instance _root_.'+namespace+'.'+enum+'.instDiscriminant :\n    Aeneas.Std.Discriminant '+enum+' Isize where\n  read_discriminant := '+enum+'.read_discriminant\n'
        new=block+registration
        assert new.replace(registration,'')==block
        replacements.append((new,match.group(0)))
        return new
    out=pattern.sub(sub,text)
    assert replacements,(namespace,'missing discriminant annotation')
    inverse=out
    for new,old in replacements:assert inverse.count(new)==1;inverse=inverse.replace(new,old,1)
    assert inverse==text
    return out.encode()
