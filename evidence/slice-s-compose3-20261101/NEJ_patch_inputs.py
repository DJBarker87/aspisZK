from pathlib import Path
E=Path(__file__).resolve().parent

def oracle_parts():
    p=(E.parent/'slice-s-compose2-20261029/NEE_K005-NEE_oracle.patch').read_text()
    first,hook=p.split('--- a/',1)
    body='\n'.join(l[1:] for l in first.splitlines()[3:] if l.startswith('+'))+'\n'
    pure=body[:body.index('#[derive(Clone,Copy,Debug,PartialEq,Eq)]')]
    return pure.replace('NEE_','NEJ_'),'--- a/'+hook.replace('NEE_','NEJ_')
