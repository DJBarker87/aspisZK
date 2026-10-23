import re
def clean(s):
 s=re.sub(r'/\*[\s\S]*?\*/','',s)
 s=re.sub(r'/-[\s\S]*?-/', '',s)
 s=re.sub(r'(?m)^--[^\n]*\n','',s)
 # Attribute payloads may contain nested discriminant value lists.
 def attrs(text):
  out='';i=0
  while True:
   a=text.find('@[',i)
   if a<0:return out+text[i:]
   out+=text[i:a];j=a+2;depth=1
   while depth:
    depth+=(text[j]=='[')-(text[j]==']');j+=1
   block=text[a+2:j-1]
   disc=re.search(r'discriminant\s+\w+\s+\[[^]]*\]',block)
   if disc:out+='@['+disc[0]+']'
   i=j
 s=attrs(s)
 s=re.sub(r'(?m)^set_option[^\n]*\n','',s)
 s=re.sub(r'(?m)^import[^\n]*\n','',s)
 return s
