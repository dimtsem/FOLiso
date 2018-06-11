from fics import FiniteInverseCategory as fic
from networkx import MultiDiGraph
import sys

def sst(n):
    S = MultiDiGraph()
    morphisms = [('X'+str(m+1),'X'+str(m),'d'+str(m)+str(i)) for m in range(n) for i in range(m+2)]
    relations = []
    if n > 1:
        relations = [(('X'+str(m+2),'X'+str(m),'d'+str(m+1)+str(j)+'d'+str(m)+str(i)),\
                      ('X'+str(m+2),'X'+str(m),'d'+str(m+1)+str(i)+'d'+str(m)+str(j-1)))
                     for m in range(n-1) for j in range(1,m+3) for i in range(j)]
    S.add_edges_from(morphisms)
    return fic(S,relations)

if __name__=='__main__':
    modes = ['sigma','context']
    n, mode = sys.argv[1:]
    if mode not in modes:
        raise ValueError(mode+' is not an available mode. The available modes are: '+','.join(modes))
    if mode == 'sigma':
        sst(int(n)).UniMathDataShape('sst_'+str(n))
    if mode == 'context':
        sst(int(n)).UniMathDataShapeContext('sst_'+str(n))