from math import sqrt,log,exp
from functools import lru_cache

def bisect(fun,a,b,target=0):
 for _ in range(70):
  c=(a+b)/2
  if fun(c)<target:a=c
  else:b=c
 return (a+b)/2

@lru_cache(None)
def params(C):
 q=bisect(lambda q:log(q)+2/3*(q**3-1),1,C,log(C))
 s0=2/sqrt(q**4+2*q); lam=s0**3/4
 pole=2/3+s0**3*(2-q**3-q**6)/6
 return q,s0,lam,pole

@lru_cache(None)
def field(C,f,b):
 q,s0,lam,pole=params(C);g=sqrt(lam*b)
 c=-2*lam*log(s0*s0/2)
 if f<g/C:n=C
 elif f>g:n=1
 else:n=0
 if n:
  I=b*b+4*n*f
  S=bisect(lambda s:s*s+4*sqrt(lam*s),0,max(4,I+1),I)
  G=sqrt(lam*S)
  P=(2*G/S-S)/4
  ci=2*lam*log((G/n)/(s0*s0/2))+S*G/3-S**3/6
  T=n*f*b+b**3/12+ci
  Tf=n*b+4*n*P; Tb=n*f+b*b/4+2*b*P
  g=n*f;gf=n;gb=0
 else:
  T=2*lam*log(f)+4/3*b*g-b**3/12+c
  Tf=2*lam/f; Tb=2*g-b*b/4
  gf=0;gb=g/(2*b)
 T-=pole*b/2;Tb-=pole/2
 return T,Tf,Tb,g,gf,gb,n

def coeffs(C,f,b,K):
 T,Tf,Tb,g,gf,gb,n=field(C,f,b)
 a=g/f
 A=f*K*K+K*(-2*Tb+2*g-b*b/2)+b*Tf-g*g/f
 B=2*(b*gf-2*K*gb)+2*T/f-2*b*g/f-K*b
 V=2*a
 return A,B,V,n,T

def angular(C,f,b,K,t,mode):
 T,Tf,Tb,g,gf,gb,n=field(C,f,b)
 if mode=='minus-b':c=-b/2;cf=0;cb=-.5
 elif mode=='minus-b-half':c=-b/4;cf=0;cb=-.25
 elif mode=='minus-b-double':c=-b;cf=0;cb=-1
 elif mode=='zero':c=cf=cb=0
 U=t*t/(1+t*t);V=1/(1+t*t)**2
 Pf=Tf+2*gf*t+cf*U
 Pb=Tb+2*gb*t+cb*U
 Pr=2*T+2*g*t+2*c*t**4*V
 Pv=2*g+2*c*t*V
 H=b*Pf+t/f*Pr-b*t/f*Pv-Pv*Pv/(4*f)+K*(-2*Pb+Pv-b*t-b*b/2)+f*K*K
 return H

if __name__=='__main__':
 for C in [2,2.25,2.5,3,3.5,4]:
  worst={m:(1e10,None) for m in ['zero','minus-b','minus-b-half','minus-b-double']}
  for i in range(17):
   b=2*i/17
   for j in range(17):
    f=(4-b*b)/4*(1/C+(1-1/C)*j/16)
    for k in range(17):
     K=1+(C-1)*k/16
     for t in [-10,-4,-2,-1,-.5,-.25,-.1,0,.1,.25,.5,1,2,4,10]:
      for m in worst:
       h=angular(C,f,b,K,t,m)/(1+t*t)
       if h<worst[m][0]:worst[m]=(h,(f,b,K,t))
  print(C,params(C),worst,flush=True)
