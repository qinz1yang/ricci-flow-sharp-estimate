from fractions import Fraction as Q
from math import sqrt,exp
from itertools import permutations

def trim(p):
 while len(p)>1 and p[-1]==0:p.pop()
 return p

def add(p,q):return trim([(p[i] if i<len(p) else 0)+(q[i] if i<len(q) else 0) for i in range(max(len(p),len(q)))])
def neg(p):return [-a for a in p]
def sub(p,q):return add(p,neg(q))
def mul(p,q):
 out=[Q(0)]*(len(p)+len(q)-1)
 for i,a in enumerate(p):
  for j,b in enumerate(q):out[i+j]+=a*b
 return trim(out)
def sc(c,p):return [c*a for a in p]
def pw(p,n):
 o=[Q(1)]
 for i in range(n):o=mul(o,p)
 return o

def der(p):return [i*p[i] for i in range(1,len(p))] or [Q(0)]
def integ(p):return sum((a/Q(i+1) for i,a in enumerate(p)),Q(0))
def val(p,x):
 o=0
 for a in reversed(p):o=o*x+a
 return o
w=[Q(0),Q(1),Q(-1)]
def geom(t):
 K=[2+2*t,-12*t,12*t]
 f=sc(2,sub(w,sc(t,pw(w,2))))
 b=der(f)
 return K,f,b

def pair(t,r,s):
 K,f,b=geom(t)
 def oper(r):return sub(add(mul(f,der(der(r))),sc(2,mul(b,der(r)))),mul(K,r))
 # f q_r q_s -K b f/2*(r*s'+s*r') +(fK^2-Kb^2/2)*r*s
 return integ(add(sub(mul(f,mul(oper(r),oper(s))),sc(Q(1,2),mul(mul(mul(K,b),f),add(mul(r,der(s)),mul(s,der(r)))))),mul(sub(mul(f,pw(K,2)),sc(Q(1,2),mul(K,pw(b,2)))),mul(r,s))))
def coeffs(vals):
 # vals at tau=0,1,-1,2; cubic
 z,p,n,t=vals
 c2=(p+n)/2-z
 d=(p-n)/2
 c3=(t-z-4*c2-2*d)/6
 return [z,d-c3,c2,c3]
def polyPair(r,s):return trim(coeffs([pair(Q(t),r,s) for t in [0,1,-1,2]]))
def det(m):
 n=len(m);out=[Q(0)]
 for perm in permutations(range(n)):
  sign=(-1)**sum(perm[i]>perm[j] for i in range(n) for j in range(i+1,n))
  p=[Q(sign)]
  for i,j in enumerate(perm):p=mul(p,m[i][j])
  out=add(out,p)
 return trim(out)
def bisect(p,a,b):
 for i in range(70):
  c=(a+b)/2
  if val(p,a)*val(p,c)<=0:b=c
  else:a=c
 return (a+b)/2
if __name__=='__main__':
 print('CK',((5+sqrt(13))/3)**(1/3)*exp((4+2*sqrt(13))/9))
 for n in [2,3,4]:
  bs=[pw(w,i) for i in range(n)]
  m=[[polyPair(r,s) for s in bs] for r in bs]
  print('n',n,'matrix',[[list(map(str,x)) for x in row] for row in m])
  d=det(m)
  print('det',list(map(str,d)))
  roots=[]
  for i in range(200):
   a=i/100;b=(i+1)/100
   if val(d,a)*val(d,b)<0:
    rt=bisect(d,a,b);roots.append((rt,(2+2*rt)/(2-rt)))
  print('roots',roots)
