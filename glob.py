from fics import FiniteInverseCategory as fic
from networkx import MultiDiGraph
import sys

def Glob(n):
    Glob = MultiDiGraph()
    s_morphisms = [('X'+str(m+1),'X'+str(m),'s'+str(m)) for m in range(n)]
    t_morphisms = [('X'+str(m+1),'X'+str(m),'t'+str(m)) for m in range(n)]
    morphisms = s_morphisms + t_morphisms
    relations = []
    if n > 1:
        ssts_relations = [(('X'+str(m+2),'X'+str(m),'s'+str(m+1)+'s'+str(m)),('X'+str(m+2),'X'+str(m),'t'+str(m+1)+'s'+str(m)))
                     for m in range(n-1)]
        sttt_relations = [(('X'+str(m+2),'X'+str(m),'s'+str(m+1)+'t'+str(m)),('X'+str(m+2),'X'+str(m),'t'+str(m+1)+'t'+str(m)))
                     for m in range(n-1)]
        relations = ssts_relations + sttt_relations
    Glob.add_edges_from(morphisms)
    return fic(Glob,relations)

if __name__=='__main__':
    modes = ['sigma','context']
    n, mode = sys.argv[1:]
    if mode not in modes:
        raise ValueError(mode+' is not an available mode. The available modes are: '+','.join(modes))
    if mode == 'sigma':
        Glob(int(n)).UniMathDataShape('glob_'+str(n))
    if mode == 'context':
        Glob(int(n)).UniMathDataShapeContext('glob_'+str(n))
        
    