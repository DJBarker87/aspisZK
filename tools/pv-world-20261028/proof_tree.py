"""Emit finite named bind/case proofs from the reservation's source tree.
No repeat, simplifier search, evaluation, or increased prover options.
"""
import re

def proof(lines,names,short,primitive_labels=()):
    def indent(s):return len(s)-len(s.lstrip())
    counter=0
    def block(i,base,level):
        nonlocal counter
        out=[];pad=' '*level
        while i<len(lines) and indent(lines[i])>=base:
            line=lines[i];t=line.strip()
            if indent(line)!=base or t.startswith('| '):break
            m=re.match(r'let (.*?) ←(.*)$',t)
            if m:
                var,expr=m.groups();parts=[expr.strip()];i+=1
                while i<len(lines) and indent(lines[i])>base:
                    parts.append(lines[i].strip());i+=1
                expr='\n'.join(x for x in parts if x)
                inline=next((n for old,n in zip(names,short) if expr.startswith(old) and expr[len(old):len(old)+1].isspace()),None)
                law='erase_'+inline if inline else 'erase_perform' if expr.split()[0] in primitive_labels else 'erase_invoke'
                out += [pad+'try dsimp only',pad+'rw [erase_bind,'+law+']',pad+'apply source_bind_congr']
                if var.startswith('('):out.append(pad+'rintro ⟨'+var[1:-1]+'⟩')
                else:out.append(pad+'intro '+var)
                continue
            if t.startswith('let '):
                i+=1
                while i<len(lines) and indent(lines[i])>base:i+=1
                continue
            if t.startswith('match '):
                discr=t[len('match '):-len(' with')]
                out += [pad+'try dsimp only',pad+'cases '+discr+' with'];i+=1
                while i<len(lines) and indent(lines[i])==base and lines[i].lstrip().startswith('| '):
                    branch=lines[i].strip()[2:].split('=>')[0].strip();pieces=branch.split();ctor=pieces[0].split('.')[-1]
                    args=[]
                    for a in pieces[1:]:
                        if a=='_':counter+=1;a='unused'+str(counter)
                        args.append(a)
                    out.append(pad+'| '+ctor+(' '+' '.join(args) if args else '')+' =>')
                    child,i=block(i+1,base+2,level+2);out+=child
                return out,i
            if t.startswith('ok '):out.append(pad+'rfl');return out,len(lines) if i+1==len(lines) else advance(i,base)
            parts=[t];i+=1
            while i<len(lines) and indent(lines[i])>base:parts.append(lines[i].strip());i+=1
            expr='\n'.join(parts)
            inline=next((n for old,n in zip(names,short) if expr.startswith(old) and expr[len(old):len(old)+1].isspace()),None)
            out.append(pad+'exact '+('erase_'+inline+' ops _' if inline else 'erase_perform ops _' if expr.split()[0] in primitive_labels else 'erase_invoke ops _ _'))
            return out,i
        return out,i
    def advance(i,base):
        i+=1
        while i<len(lines) and indent(lines[i])>base:i+=1
        return i
    out,end=block(0,2,2)
    assert end==len(lines),(end,len(lines),lines[end:])
    return '\n'.join(out)
