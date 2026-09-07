#!/usr/bin/env python3
"""Independent arbitrary-integer polynomial check, no production field imports."""
P=2**31-1
def trim(a):
    while a and a[-1]==0:a.pop()
    return a
def sub(a,b):
    return trim([((a[i] if i<len(a) else 0)-(b[i] if i<len(b) else 0))%P for i in range(max(len(a),len(b)))])
def rem(a,b):
    a=a[:]
    while len(a)>=len(b):
        k=len(a)-len(b);v=a[-1]*pow(b[-1],P-2,P)%P
        for j,x in enumerate(b):a[j+k]=(a[j+k]-v*x)%P
        trim(a)
    return a
def mul(a,b,f):
    c=[0]*(len(a)+len(b)-1)
    for i,x in enumerate(a):
        for j,y in enumerate(b):c[i+j]=(c[i+j]+x*y)%P
    return rem(trim(c),f)
def power(a,n,f):
    r=[1]
    while n:
        if n&1:r=mul(r,a,f)
        a=mul(a,a,f);n>>=1
    return r
def gcd(a,b):
    while b:a,b=b,rem(a,b)
    return [x*pow(a[-1],P-2,P)%P for x in a]
f=[P-6,P-1,0,0,0,1];x=[0,1]
assert power(x,P**5,f)==x
assert gcd(sub(power(x,P,f),x),f)==[1]
# u^2=2+i, i^2=-1 implies u^4-4u^2+5=0.
g=[5,0,P-4,0,1]
assert power(x,P**4,g)==x
assert gcd(sub(power(x,P**2,g),x),g)==[1]
assert power(x,(P**4-1)//2,g)==[P-1]
print('independent Python polynomial Rabin checks: quintic and QM31 quartic irreducible; u nonsquare; octic tower valid')
