from ck_angular_test import angular,params
from polynomial_test import geom,val
from fractions import Fraction as Q
from math import sqrt
for tau in [Q(1,2),Q(2,3),Q(4,5),Q(1),Q(11,10)]:
 C=float((2+2*tau)/(2-tau)); kap=float(2-tau)
 K,f,b=geom(tau)
 worst={m:(1e10,None) for m in ['zero','minus-b','minus-b-half']}
 for i in range(1,50):
  x=i/100
  ff=float(val(f,x))*kap;bb=float(val(b,x));kk=float(val(K,x))/kap
  for t in [-10,-4,-2,-1,-.5,-.25,-.1,0,.1,.25,.5,1,2,4,10]:
   for m in worst:
    h=angular(C,ff,bb,kk,t,m)/(1+t*t)
    if h<worst[m][0]:worst[m]=(h,(x,ff,bb,kk,t))
 print('ACTUAL',str(tau),C,worst,flush=True)
# actual tau=2/3, rational x=1/8,t=1/2
K,f,b=geom(Q(2,3));x=Q(1,8);kap=Q(4,3)
ff=kap*val(f,x);bb=val(b,x);kk=val(K,x)/kap
print('RATIONAL_POINT',ff,bb,kk,'params',params(2.5))
for m in ['zero','minus-b','minus-b-half']:
 print(m,angular(2.5,float(ff),float(bb),float(kk),.5,m))
