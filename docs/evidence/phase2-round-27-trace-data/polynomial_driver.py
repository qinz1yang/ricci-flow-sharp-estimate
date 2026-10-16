from polynomial_test import *
from pathlib import Path
import json
s=Path(__file__).parent
records=[]
for parity in [0,1]:
 for n in [2,3,4]:
  basis=[pw(w,i) for i in range(n)]
  if parity:basis=[mul([Q(-1,2),Q(1)],r) for r in basis]
  matrix=[[polyPair(r,t) for t in basis] for r in basis]
  determinant=det(matrix)
  roots=[]
  for i in range(200):
   lo=i/100;hi=(i+1)/100
   if val(determinant,lo)*val(determinant,hi)<0:
    root=bisect(determinant,lo,hi)
    roots.append({'tau_approx':root,'ratio_approx':(2+2*root)/(2-root)})
  records.append({'parity':'odd' if parity else 'even','dimension':n,
    'exact_action_matrix':[[list(map(str,p)) for p in row] for row in matrix],
    'exact_determinant_coefficients':list(map(str,determinant)),
    'numerical_sign_change_roots':roots})
(s/'polynomial-results.json').write_text(json.dumps({
 'scope':'Exact Fraction arithmetic and exploratory floating bisection only; not a kernel theorem or global positivity/absence-of-roots proof. No improved upper barrier produced.',
 'records':records},indent=2)+'\n')
for rec in records:print(rec['parity'],rec['dimension'],rec['numerical_sign_change_roots'])
