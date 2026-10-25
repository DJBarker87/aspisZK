"""ELF64 little-endian metadata from stable catalog FDs; never execute a tool."""
import os
import struct
from FinalNativeGate_bounded import CatalogError


def dependencies(reader,path):
    with reader.opened(path) as (fd,canonical,entry):
        spent=0
        def read(off,size):
            nonlocal spent
            spent+=size
            if spent>entry['size']:raise CatalogError('ELF metadata byte budget (one file size)')
            reader.tick()
            if min(off,size)<0 or off+size>entry['size']:raise CatalogError('ELF range')
            data=os.pread(fd,size,off)
            if len(data)!=size:raise CatalogError('ELF short read')
            return data
        head=read(0,min(64,entry['size']))
        if head[:4]!=b'\x7fELF':return dict(path=path,format='non-ELF',deferred='script/archive/data role requires explicit catalog assessment')
        if len(head)!=64 or head[:6]!=b'\x7fELF\x02\x01':raise CatalogError('unsupported ELF ABI')
        off=struct.unpack_from('<Q',head,32)[0];stride,count=struct.unpack_from('<HH',head,54)
        if stride!=56 or count==65535:raise CatalogError('unsupported extended program headers')
        loads=[];dynamic=[];interp=[]
        for i in range(count):
            p=struct.unpack('<IIQQQQQQ',read(off+i*stride,56))
            kind,_,offset,vaddr,_,size,_,_=p
            if kind==1:loads.append((vaddr,offset,size))
            if kind==2:dynamic.append((offset,size))
            if kind==3:
                if size>4096:raise CatalogError('interpreter path exceeds Linux path bound')
                interp.append(read(offset,size).rstrip(b'\0').decode('ascii'))
        strings=None;length=None;needed=[];search=[]
        for offset,size in dynamic:
            if size%16:raise CatalogError('dynamic alignment')
            ended=False
            for i in range(size//16):
                tag,value=struct.unpack('<qQ',read(offset+16*i,16))
                if tag==0:ended=True;break
                if tag==5:strings=value
                if tag==10:length=value
                if tag==1:needed.append(value)
                if tag in (15,29):search.append((tag,value))
            if not ended:raise CatalogError('unterminated dynamic table')
        def string(index):
            if strings is None or length is None or index>=length:raise CatalogError('missing/outside string table')
            choices=[o+strings-v for v,o,n in loads if v<=strings and strings+length<=v+n]
            if len(choices)!=1:raise CatalogError('ambiguous ELF string mapping')
            out=bytearray()
            for i in range(min(length-index,4096)):
                ch=read(choices[0]+index+i,1)
                if ch==b'\0':return out.decode('ascii')
                out.extend(ch)
            raise CatalogError('unterminated/oversize ELF name')
        return dict(path=path,canonical=canonical,format='ELF64LE',machine=struct.unpack_from('<H',head,18)[0],
                    interpreter=interp,needed=[string(i) for i in needed],search=[(t,string(i)) for t,i in search])
