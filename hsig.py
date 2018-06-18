from fics import FiniteInverseCategory, FICStructure, FICStructureHomomorphism, TypedFunction
from collections import defaultdict
from networkx import MultiDiGraph

class hSignature(FiniteInverseCategory):
    '''
    An h-signature from a mathematical point of view is a fic with extra structure.
    
    This extra structure consists in a natural number (possibly infinity) attached to every object and
    three specified "logical" objects (isomorphism sorts, reflexivity sorts, and transport sorts) and several types
    of "logical" morphisms associated to these logical sorts. 
    
    For more details cf. Tsementzis, "First-Order Logic with Isomorphism", Definition 3.2
    
    There is an obvious forgetful functor hSig -> FIC and there is also a canonical functor FIC -> hSig that takes a fic
    to the h-signature all of whose objects have infinite h-level (i.e. are "untruncated types").
    
    The implementation is based on these functors in that an instance of hSignature is obtained by adding attributes
    to an instance of FiniteInverseCategory.
    '''

    def __init__(self, damg, relations = [], ficname='L', data=None, **attr):
        '''
        An h-signature (hsig) is initialized as a fic with extra structure.
        
        This extra structure is entirely given through node attributes on the underlying graph
        of the fic, and therefore the input required is exactly the same as for the FiniteInverseCategory
        class.
        
        The class can also be initialized by passing a fic directly as [damg].
        '''
        # initialize the data as a fic, to inherit all the methods and attributes
        if isinstance(damg, FiniteInverseCategory):
            FiniteInverseCategory.__init__(self, damg.underlying, damg.relations, damg.ficname)
        else:
            FiniteInverseCategory.__init__(self, damg, relations, ficname, data=None, **attr)
        # set the name of the h-signature, which is distinct from the name of the underlying fic
        self.hsigname = 'h_'+self.ficname
        # set the h-level and logical types of sorts
        self.hlevel = defaultdict(lambda : None)
        self.logicaltype = defaultdict(lambda : None)
        for K in self.objects:
            self.hlevel[K] = self.underlying.nodes(data='hlevel')[K]
            if not self.hlevel_iswelldefined(K):
                raise ValueError('Invalid h-level entry for sort '+K)
            self.logicaltype[K] = self.underlying.nodes(data='logicaltype')[K]
            if not self.logicalsort_iswelldefined(K):
                raise ValueError('The logical sort '+K+' is not well-formed')
                
    def islogical_morphism(self,f):
        '''
        Checks if a morphism is a logical morphism, i.e. if it is a morphism with a logical sort as its domain.
        '''
        return self.logicaltype[self.dom[f[2]]] is not None
    
    def hlevel_reduce(self,h,k):
        '''
        Reduce the h-level of h by k.
        '''
        if h is None:
            return None
        else:
            return h-k
    
    def hlevel_iswelldefined(self,K):
        '''
        Test to determine whether the h-level of K is well-defined (i.e. whether it is None or an int).
        '''
        if self.hlevel[K] is None:
            return True
        else:
            return isinstance(self.hlevel[K],int)
        
    def logicalsort_iswelldefined(self,K):
        '''
        Placeholder for developing tests to determine whether a logical sort K is well-defined.
        
        NOTE: Currently inert in that it only returns True.
        '''
        if self.logicaltype[K] == 'iso':
            return True
        if self.logicaltype[K] == 'refl':
            return True
        if self.logicaltype[K] == 'trans':
            return True
        else:
            return True
    
    def add_iso_sort(self,K):
        '''
        Extends the hsig by adding an isomorphism sort for an object K already in the hsig.
        
        For details and intuition cf. Tsementzis, "First-Order Logic with Isomorphism", Remark 3.3
        '''
        newobjects = [('iso_'+K,{'hlevel':self.hlevel_reduce(self.hlevel[K],1),'logicaltype':'iso'})]
        newmorphisms = [('iso_'+K,K,'s_'+K),('iso_'+K,K,'t_'+K)]
        newrelations = self.relations
        for g in self.coslice[K]:
            newrelations.append((('iso_'+K,self.cod[g[2]],'s_'+K+g[2]),('iso_'+K,self.cod[g[2]],'t_'+K+g[2])))
        return hSignature(self.extend(newmorphisms,newrelations,newobjects))
          
    def add_refl_sort(self,K):
        '''
        Extends the hsig by adding an isomorphism sort and a reflexivity sort for an object K already in the hsig.
        
        For details and intuition cf. Tsementzis, "First-Order Logic with Isomorphism", Remark 3.3
        '''
        # first add the isomorphism sort of K
        isosig = self.add_iso_sort(K)
        newobjects = [('refl_'+K,{'hlevel':self.hlevel_reduce(self.hlevel[K],2),'logicaltype':'refl'})]
        newmorphisms = [('refl_'+K,'iso_'+K,'r_'+K)]
        newrelations = isosig.relations
        newrelations.append((('refl_'+K,K,'r_'+K+'s_'+K),('refl_'+K,K,'r_'+K+'t_'+K)))
        return hSignature(isosig.extend(newmorphisms,newrelations,newobjects))
    
    def add_trans_sort(self,f):
        '''
        Extends the hsig by adding a transport sort for a (top-level) morphism f : A -> K already in the hsig.
        
        For details and intuition cf. Tsementzis, "First-Order Logic with Isomorphism", Remark 3.3
        '''
        if not self.istop_morphism(f):
            raise ValueError('Can only add transport sorts for top-level morphisms')
        # name the domain and codomain of f for convenience ...
        K = self.cod[f[2]]
        A = self.dom[f[2]]
        # ... andadd the isomorphism sort of the codomain K of f
        isosig = self.add_iso_sort(K)
        newobjects = [('trans_'+f[2],{'hlevel':self.hlevel_reduce(self.hlevel[A],1),'logicaltype':'trans'})]
        newmorphisms = [('trans_'+f[2],'iso_'+K,'e_'+f[2]),('trans_'+f[2],A,f[2]+str(1)),\
                                   ('trans_'+f[2],A,f[2]+str(2))]
        newrelations = isosig.relations
        for g in self.coslice[K]:
            newrelations.append((('trans_'+f[2],self.cod[g[2]],f[2]+str(1)+f[2]+g[2]),\
                              ('trans_'+f[2],self.cod[g[2]],f[2]+str(2)+f[2]+g[2])))
        for g in [g for g in self.coslice[A] if g != f]:
            newrelations.append((('trans_'+f[2],self.cod[g[2]],f[2]+str(1)+g[2]),\
                              ('trans_'+f[2],self.cod[g[2]],f[2]+str(2)+g[2])))
        newrelations.append((('trans_'+f[2],K,'e_'+f[2]+'s_'+K),('trans_'+f[2],K,f[2]+str(1)+f[2])))
        newrelations.append((('trans_'+f[2],K,'e_'+f[2]+'t_'+K),('trans_'+f[2],K,f[2]+str(2)+f[2])))
        return hSignature(isosig.extend(newmorphisms,newrelations,newobjects))
        
        
    
    
    