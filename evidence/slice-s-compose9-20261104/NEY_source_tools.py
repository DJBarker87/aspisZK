"""Balanced call-head rewrite used only for frozen-body oracle instrumentation."""
def calls(text,old,new,extra):
 needle=old+'(';pos=0
 while True:
  a=text.find(needle,pos)
  if a<0:return text
  start=a+len(needle);depth=1;j=start
  while depth:
   if text[j]=='(':depth+=1
   elif text[j]==')':depth-=1
   j+=1
  args=text[start:j-1].rstrip().rstrip(',')
  replacement=new+'('+args+','+extra+')'
  text=text[:a]+replacement+text[j:];pos=a+len(replacement)
