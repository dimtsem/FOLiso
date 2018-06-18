import networkx as nx
from networkx.classes.graph import Graph
from networkx.classes.digraph import DiGraph
from networkx.classes.multigraph import MultiGraph
from networkx.classes.multidigraph import MultiDiGraph
from networkx.classes.coreviews import MultiAdjacencyView
from networkx.classes.reportviews import OutMultiEdgeView, InMultiEdgeView, DiMultiDegreeView, OutMultiDegreeView, InMultiDegreeView
from networkx.exception import NetworkXError
from networkx.algorithms.dag import is_directed_acyclic_graph as isdag
from networkx.algorithms.dag import transitive_closure
from collections import defaultdict


class TypedFunction():
    '''
    An auxilliary class for "typed functions", i.e. functions with a fixed domain and 
    codomain. They are useful as the value of arrows in Set-valued functors.
    '''
    def __init__(self,domain,codomain,function):
        if isinstance(domain,list) and isinstance(codomain,list):
            self.domain = domain
            self.codomain = codomain
        else:
            raise ValueError('Domain and Codomain must be a list')
        if self.domain == []:
            return self
        elif isinstance(function,dict):
            self.app = function
        else:
            raise ValueError('Function must be in the form of an "{input:image}" dict')
        wellformed = True
        for a in self.app.keys():
            wellformed = (a in self.domain) and (self.app[a] in self.codomain)
        if not wellformed:
            raise ValueError('The function contains values outside its (co)domain')
    
    def istotal(self):
        '''
        Checks if the function is total, i.e. if it takes a value for every element in
        the domain.
        '''
        return set(self.domain) == set(self.app.keys())
    
    def issurjective(self):
        '''
        Checks if the function is surjective, i.e. if every value in its codomain is
        the image of a value in its domain.
        '''
        return set(self.codomain) == set(self.app.values())
    
    def compose(self,typedfunction):
        '''
        Postcomposes with a given TypedFunction, returning the composite TypedFunction
        '''
        if not isinstance(typedfunction,TypedFunction):
            raise ValueError('Can only compose typed functions with each other: '+\
                             str(typedfunction)+' is not a TypedFunction')
        composedfunction = {}
        for a in self.domain:
            try:
                composedfunction[a] = typedfunction.app[self.app[a]]
            except:
                pass
        return TypedFunction(self.domain,typedfunction.codomain,composedfunction)
    
    def funextequal(self,typedfunction):
        '''
        Checks if two typed functions are equal by checking if they take the same values
        over the same range ("functional extensionality").
        '''
        if not ((self.domain == typedfunction.domain) and\
           (self.codomain == typedfunction.codomain)):
            return false
        result = True
        for x in self.domain:
            if self.app[x] != typedfunction.app[x]:
                result = False
        return result
                    

class FiniteInverseCategory(MultiDiGraph):
    '''
    An implementation of finite inverse categories as a data structure building on the NetworkX library.
    
    A finite inverse category (fic) from a mathematical point of view is a finite skeletal category with
    no non-identity endomorphisms.

    An alternative definition is as a pair (G,comp) where G = (V,E) is a finite transitive directed 
    acyclic  multigraph (damg) and comp is an associative binary operation on E that takes two
    "composable" edges to their "composite". This is the definition on which this implementation is based.

    It is important to note that every fic has an underlying damg but for any given damg there are
    multiple non-isomorphic fic structures we can put on it.
    
    The focus of this implementation is to allow every fic (and fic-structure/homomorphisms) to be "interpreted"
    into proof assistants by producing files that type-check in each proof assistant. For example, each fic L
    in this implementation can be "interpreted" into a L.v file which contains the "Sigma-type" corresponding to 
    L (such that L.v type-checks in Coq over the appropriate libraries.)
    
    The general procedure for defining fics in this implementation is to define the underlying damg as a
    NetworkX MultiDiGraph object, express the relations that one wants, and then feed this information to 
    the FiniteInverseCategory class. Note that one need not ensure that the graph is transitive, as this will be
    taken care of automatically, but the graph will have to be a da(m)g, otherwise __init__ will throw an error.
    
    --Initialization Parameters--
    
    damg: the underlying graph of the fic, which must be a da(m)g, otherwise __init__ will throw an error.
    
    relations: a list of tuples of the form ((domain,codomain,f),(domain,codomain,g)) representing relations 
               between morphisms f,g: domain -> codomain. Errors will be thrown if f,g are not (composites of)
               edges in the underlying da(m)g or if they do not have the same domain and codomain.
               
    data, attr: placeholders anticipating the hsignature class that will implement the fics with extra structure 
                that form the basic objects of study of FOL with isomorphism. If one works only with fics then 
                these can be ignored.
                
    -------------- 

    As far as the implementation details are concerned, there are some things to note:

    *) In general, a particular fic will not be very large, so we can be wasteful with 
       memory allocation. (On the other hand, fic-structures will require a lot of memory
       so more caution will be required there.)
    *) The __init__s have been made very long to emulate the kind of "type-checking" that is necessary in order
       to interpret these structures into dependent type theory.
    '''
    def __init__(self, damg, relations = [], ficname='L', data=None, **attr):
        # the name of the fic
        self.ficname = ficname
        # the underlying graph of the fic
        self.underlying = damg
        # test(s) to determine if the underlying graph is indeed the underlying graph of a finite inverse category, i.e. a dag,
        # and raise error if not
        self.wellformed = isdag(self.underlying)
        if not self.wellformed:
            raise ValueError('Underlying graph is not a da(m)g')
        # define objects and morphisms of the category to be those of the underlying graph
        self.objects = list(self.underlying.nodes)
        self.morphisms = list(self.underlying.edges)
        self.morphism_names = [morphism[2] for morphism in self.morphisms]
        # define domain and codomain functions to extract from morphisms
        self.dom = {}
        for morphism in self.morphisms:
            self.dom[morphism[2]] = morphism[0]
        self.cod = {}
        for morphism in self.morphisms:
            self.cod[morphism[2]] = morphism[1]
        # define the "length" of a morphism...
        self.morlen = {}
        # ...where each primitive morphism has length 1
        for morphism in self.morphisms:
            self.morlen[morphism] = 1
        # add to state any relations given as input...
        self.relations = relations
        self.isequalto = defaultdict(lambda : [])
        # ...and add to state a dictionary that will keep track of the set of morphisms a morphism is equal to
        for rel in self.relations:
            self.isequalto[rel[0]].append(rel[1])
            self.isequalto[rel[1]].append(rel[0])
        # freely add all the composable morphisms to yield the free fic on the underlying damg
        # NB: we use diagrammatic ordering!
        composed = defaultdict(lambda : False)
        # this is the composition function, encoded as a defaultdict...
        self.comp = defaultdict(lambda : None)
        # ...and now we freely add all composites by...
        while True:
            complete = True
            # ...taking all composable pairs currently available...
            composables = [(f,g) for f in self.morphisms for g in self.morphisms 
                           if self.dom[g[2]] == self.cod[f[2]]]
            for morphism in composables:
                if not composed[morphism]:
                    # ...and defining their composite and its properties
                    composite = (self.dom[morphism[0][2]],self.cod[morphism[1][2]],morphism[0][2]+morphism[1][2])
                    self.morphisms.append(composite)
                    self.morphism_names.append(composite[2])
                    self.dom[composite[2]] = composite[0]
                    self.cod[composite[2]] = composite[1]
                    self.comp[(morphism[0],morphism[1])] = composite
                    self.morlen[composite] = self.morlen[morphism[0]] + self.morlen[morphism[1]]
                    composed[morphism] = True
                    complete = False
            # this will break the while loop if no composable pairs are left, which is guaranteed to happen because the
            # underlying graph is a dag
            if complete:
                break
        # check if any meaningless relations were given as input (this has to happen after "freely adding" the composites above)
        for rel in self.relations:
            if rel[0] not in self.morphisms or rel[1] not in self.morphisms:
                raise ValueError(rel, ' is invalid because one of the morphisms is not in the fic. ')
            elif (self.cod[rel[0][2]] != self.cod[rel[1][2]]) or (self.dom[rel[0][2]] != self.dom[rel[1][2]]):
                raise ValueError(rel, ' is invalid because these two morphisms have distinct domains or codomains. ')
        # propagate the given relations through all composites
        for length in range(1,max(self.morlen.values())):
            composables = [(f,g) for f in self.morphisms for g in self.morphisms 
                          if (self.dom[g[2]] == self.cod[f[2]]) and ((self.morlen[f] == length) or (self.morlen[g] == length))]
            for pair in composables:
                for f in self.isequalto[pair[0]]:
                    self.isequalto[self.comp[pair]].append(self.comp[(f,pair[1])])
                for f in self.isequalto[pair[1]]:
                    self.isequalto[self.comp[pair]].append(self.comp[(pair[0],f)])
        # obtain equality classes for morphisms (as the transitive closure of the self.isequalto relation)
        self.eqclass = {}
        seen = defaultdict(lambda : False)
        for f in self.morphisms:
            if not seen[f]:
                self.eqclass[f] = self.isequalto[f]
                while [g for g in self.eqclass[f] if not seen[g]]:
                    for g in [g for g in self.eqclass[f] if not seen[g]]:
                        self.eqclass[f].append(g)
                        self.eqclass[f] = list(set(self.eqclass[f] + self.isequalto[g]))
                        seen[g] = True
                # finally, set the equality class of every arrow f is equal to to be the same as f      
                for g in self.eqclass[f]:
                    self.eqclass[g] = self.eqclass[f]
        # a dictionary picking a canonical representative for each equality class of morphisms,
        # useful for the interpretation of fics.
        self.mortovar = {}
        visited = defaultdict(lambda : False)
        for f in self.morphisms:
            if not visited[f]:
                self.mortovar[f] = f
                for g in self.eqclass[f]:
                    self.mortovar[g] = f
                    visited[g] = True
                visited[f] = True
        # define the "hom sets" of the fic, i.e. the set of all morphisms between any two objects
        self.Hom = defaultdict(lambda : [])
        for A,B in [(x,y) for x in self.objects for y in self.objects]:
            self.Hom[(A,B)] = list(set([self.mortovar[f] for f in self.morphisms 
                              if (self.dom[f[2]] == A) & (self.cod[f[2]] == B)]))
        # a list of the objects sorted by level
        self.objectsbylevel = sorted(self.objects,key = self.Reedy_level)
        # a {object:list of morphisms with object as domain} dictionary called self.coslice
        self.coslice = defaultdict(lambda : [])
        seen = defaultdict(lambda : False)
        for A in self.objectsbylevel:
            for K in sorted(self.objectsbylevel, key=lambda x : -self.Reedy_level(x)):
                for f in self.Hom[(A,K)]:
                    if not seen[f]:
                        self.coslice[A].append(f)
                        seen[f] = True
                        for g in self.isequalto[f]:
                            seen[g] = True
                        for h in self.coslice[K]:
                            self.coslice[A].append(self.mortovar[self.comp[(f,h)]])
                            seen[self.comp[(f,h)]] = True
                            for k in self.isequalto[self.comp[(f,h)]]:
                                seen[k] = True
            self.coslice[A] = sorted(list(set(self.coslice[A])), key=lambda x : -self.morlen[x])            

    def isbottom(self,obj):
        '''
        Check if an object [obj] is a "bottom" or "ground" sort, i.e. if there exist
        no non-identity arrows with [obj] their domain.
        '''
        result = True
        for K in self.objects:
            if self.Hom[(obj,K)]:
                result = False
        return result
    
    def istop(self,obj):
        '''
        Check if an object [obj] is a "top-level" sort, i.e. if there exist
        no non-identity arrows with [obj] their codomain.
        '''
        result = True
        for K in self.objects:
            if self.Hom[(K,obj)]:
                result = False
        return result
    
    def istop_morphism(self,morphism):
        '''
        Check if a morphism is "top-level" or "prime", i.e. if it cannot be expressed 
        as the composite of two other morphisms.
        '''
        result = True
        if [(f,g) for f in self.morphisms for g in self.morphisms 
            if (self.dom[g[2]] == self.cod[f[2]]) and
            (self.dom[f[2]] == self.dom[morphism[2]]) and
            (self.cod[g[2]] == self.cod[morphism[2]]) and
            (self.comp[(f,g)] == morphism)]:
            result = False
        return result
    
    def Reedy_level(self,K):
        '''
        Returns the "Reedy level" r(K) of a sort K in the signature with bottom sorts set to 0. Mathematically,
        r is defined as follows:
        
        r(K) = 0 if K is a bottom sort
        r(K) = sup_{A in L, s.t. there exists non-identity K --> A}(r(A) + 1)
        '''
        if self.isbottom(K):
            return 0
        else:
            return max(list(map(self.Reedy_level,[A for A in self.objects if self.Hom[(K,A)]]))) + 1
        
    def extend(self, morphisms,relations, objects = None, newficname=None):
        '''
        Extends a fic by a list of morphisms and relations involving those new morphisms, without changing the 
        underlying fic.
        
        (An equivalent operation can be performed using a series of collages.)
        
        If newficname is not given then the new extended fic is given the same name as the fic it extends.
        '''
        underlying = self.underlying
        underlying.add_nodes_from(objects)
        underlying.add_edges_from(morphisms)
        newrelations = self.relations + relations
        if newficname is None:
            newficname = self.ficname
        return FiniteInverseCategory(underlying,relations,newficname)
        
    def makevar(self, morphism):
        '''
        Takes a morphism in the signature and returns a variable expression.
        
        NB: To be used in the interpretation into type theory.
        '''
        return str(morphism[2])+''.join(map(str,morphism[:2]))
    
    def Interp(self,K,f=None):
        '''
        Takes a an object K of the fic and returns a string representing its type
        when it is regarded as a type in the context given by the proper coslice on K.
        
        This is a proof-assistant-agnostic "interpretation" that can then be used to 
        produce correct type expressions in each particular vernacular.
        '''    
        if K not in self.objects or (f is not None and f not in self.morphisms):
            raise ValueError('You can only pass objects or morphisms '
                             ' of ',self,' to Interp')
        tyexp = []
        topmorphisms = [g for g in self.coslice[K]]
        if self.isbottom(K):
            tyexp = [(None, 'UU')]
        elif f is None:
            for g in topmorphisms:
                codtype = self.Interp(self.cod[g[2]],self.mortovar[g])
                tyexp.append((self.mortovar[g],codtype))
        else:
            if self.cod[f[2]] != K:
                raise ValueError('The codomain of ',f,' must be ',K,'.')
            incontext = defaultdict(lambda : False)
            for g in topmorphisms:
                codtype = self.Interp(self.cod[g[2]],self.mortovar[g])
                if not incontext[self.comp[(f,g)]]:
                    tyexp.append((self.mortovar[self.comp[(f,g)]],codtype))
                    incontext[self.comp[(f,g)]] = True 
        return tyexp
                    

    def UniMath(self,tyexp):
        '''
        Takes the output of self.Interp and produces a type in the UniMath vernacular.
        '''
        if tyexp[0][1] == 'UU':
            return 'UU'
        else:
            ty = ''
            for variable in tyexp:
                varapp = ' '.join([self.makevar(expr[0]) for expr in variable[1] 
                                  if expr[0] is not None])
                ty = ty+' ('+self.makevar(variable[0])+' :'\
                     ' '+str(self.cod[variable[0][2]])+' '+varapp+')'
            return '∏ '+ty+', UU'
    
    def UniMathShape(self):
        '''
        Returns a string representation of the ∑-type to which the fic corresponds to
        '''
        return '∑ '+' '.join(['('+str(K)+' : '+self.UniMath(self.Interp(K))+')' for
                              K in sorted(self.objects,key = self.Reedy_level)])+', unit'
    
    def UniMathShape_asContext(self):
        '''
        Returns a string representation of the context to which the fic corresponds to
        '''
        return '\n'.join(['Context ('+str(K)+' : '+self.UniMath(self.Interp(K))+').' for
                              K in self.objectsbylevel])
    
    def UniMathDataShape(self,filename='DataShape'):
        '''
        Produces a Coq file with [filename].v with the interpretation of the fic L as a ∑-type
        in UniMath vernacular.
        
        This requires UniMath to run in Coq.
        '''
        # open the file to write
        coqfile = open(filename+'.v', 'w')
        # write the minimum Import requirement
        coqfile.write('Require Import UniMath.Foundations.PartB. \n')
        coqfile.write('\n')    
        coqfile.write('\n')    
        # definition of the ∑-type corresponding to the given fic
        LLstring = 'Definition Data : UU := '+ self.UniMathShape()+'.'
        coqfile.write(LLstring)
    
    def UniMathDataShapeContext(self,filename='DataShape'):
        '''
        Produces a Coq file [filename].v with the interpretation of the fic L as a context
        in UniMath vernacular.
        
        This requires UniMath to run in Coq.
        '''
        # open the file to write
        coqfile = open(filename+'.v', 'w')
        # write the minimum Import requirement
        coqfile.write('Require Import UniMath.Foundations.PartB. \n')
        coqfile.write('\n')    
        coqfile.write('\n')    
        # definition of the context corresponding to the given fic
        LLstring = self.UniMathShape_asContext()
        coqfile.write(LLstring)

class FICStructure(FiniteInverseCategory):
    '''
    An L-structure for a finite inverse category L from a mathematical point of view 
    is a (Reedy fibrant) functor L -> Set_f where Set_f is the category of finite sets.
    
    For the time being, we do not encode the Reedy fibrancy into the implementation, as it
    seems like an unecessary distraction from its primary purpose.

    An L-structure can be thought of as a first-order structure analogous to the
    Sigma-structures (or "similarity types") of first-order logic. 

    From the point of view of data, an L-structure can be thought of as a "data shape"
    for the "schema" L, analogous to how a table of rows and columns can be thought of as a
    "data set" for the "schema" given by the number and type of columns in the table.

    An L-structure can also be thought of as a context of variables, or alternatively, 
    as a context in type theory and this is an important observation both for theoretical
    and practical reasons, primarily for the interpretation into type theory, done later.

    '''
    def __init__(self, fic, obdata = defaultdict(lambda : []),\
                            mordata = defaultdict(lambda : []),strucname='M'):
        # define the name of the functor representing the L-structure
        self.strucname = strucname
        # define the fic L on which the L-structure is a functor
        self.signature = fic
        # get the data for the object part of the functor
        self.obval = obdata
        # check that the values of the functor on objects/morphisms are well-formed 
        # by checking if every value refers to an object/morphism in the signature, 
        # and raise error if not
        for K in self.obval.keys():
            if K not in self.signature.objects:
                raise ValueError('Object ',K,' not in signature')
        # in the case where obdata has been provided, initialize the rest of the values
        # of object part of the functor on objects of the signature to be the empty set
        for K in [K for K in self.signature.objects if K not in self.obval.keys()]:
                self.obval[K] = []
        self.morval = mordata
        for f in self.morval.keys():
            if f not in self.signature.morphisms:
                raise ValueError('Morphism ',f,' not in signature')
            elif not isinstance(self.morval[f],TypedFunction):
                raise ValueError('The value of ',f,' is not a TypedFunction')
        # now we test whether the values of each non-bottom sort K are such that each 
        # get assigned a value by the values of any of the top-level morphisms out of
        # K, which is a requirement for the functor to be well-defined
        for K in [K for K in self.signature.objects if not self.signature.isbottom(K)]:
            for x in self.obval[K]:
                for f in [f for f in self.signature.morphisms
                          if (self.signature.dom[f[2]] == K) and
                             (self.signature.istop_morphism(f))]:
                    try:
                        assert self.morval[f].app[x] is not None
                    except:
                        raise ValueError('Ill-formed structure. Either some '
                              'term lacks a value under a function or some '
                              'function is ill-defined, or ill-typed')
        # we define the value of composites to be the composite of their values
        for f,g in [(f,g) for f in self.morval.keys()
                          for g in self.morval.keys() 
                          if self.signature.dom[g[2]] == self.signature.cod[f[2]]]:
            self.morval[self.signature.comp[(f,g)]] = self.morval[f].compose(self.morval[g])
        # we make sure that equal morphisms get sent to equal functions
        for f in self.signature.morphisms:
            for g in self.signature.eqclass[f]:
                if not self.morval[f].funextequal(self.morval[g]):
                    raise ValueError('Not a functor: equal arrows have not been sent to equal functions.')       
        
    def dep(self, K, x):
        '''
        Takes as input an object [K] of L and a term [x] in M(K) and returns a dict of the 
        [dep]endencies of x i.e. the image of x under M(f) for any arrow f: K -> K' in L
        
        The output is a dictionary [depdict] such that depdict[f] is the value of x under
        M(f).
        '''
        if K not in self.signature.objects:
            raise ValueError(K+' is not an object of the underlying signature.')
        if x not in self.obval[K]:
            raise ValueError(x+' is not in a term of the L-structure at '+K)
        depdict = {}
        for f in self.signature.coslice[K]:
            depdict[f[2]]=self.morval[f].app[x]
        return depdict
        
            
    def yoneda(self, obj):
        '''
        Takes an object [obj] of the underlying fic L and returns the L-structure 
        corresponding to the Yoneda functor as [obj].
        '''
        if obj not in self.signature.objects:
            raise ValueError('Object '+str(obj)+' not in signature.')
        # initialize the dictionary for the value of y(obj) on objects
        obdata = {}
        for K in [K for K in self.signature.objects if self.signature.Hom[(obj,K)]]:
            obdata[K] = self.signature.Hom[(obj,K)]
        # add the identity morphism -- NB: this step is necessary due to the current
        # design choice not to add identity morphisms by hand.
        obdata[obj] = ['id_'+str(obj)]
        # initialize the dictionary for the value of y(obj) on morphisms
        mordata = {}    
        for f in self.signature.morphisms:
            if obdata[self.signature.dom[f[2]]] and obdata[self.signature.cod[f[2]]]:
                yA = obdata[self.signature.dom[f[2]]]
                yK = obdata[self.signature.cod[f[2]]]
                funcdict = {}
                for g in yA:
                    if g in obdata[obj]:
                        funcdict[g] = self.signature.mortovar[f]
                    else:
                        funcdict[g] = self.signature.mortovar[self.signature.comp[(g,f)]]
                mordata[f] = TypedFunction(yA,yK,funcdict)
        return FICStructure(self.signature,obdata,mordata)
    
    def reducedyoneda(self, obj):
        '''
        Same as yoneda except the value at [obj] is empty.
        '''
        yhat = self.yoneda(obj)
        yhat.obval[obj] = []
        return yhat
    
    def collage(self):
        '''
        Returns the "collage" (or "fic extension") L*M of L with the L-structure M.
        
        Mathematically, the collage L*M is defined as the fic with ob(L*M) = ob(L) + {K_M}
        such that yK_M \iso M, i.e. the fic which adds one object K_M to L whose coslice is 
        isomorphic to M
        
        For more details see Tsementzis-Weaver, "Finite Inverse Categories as Signatures" (2017)
        '''
        underlying = self.signature.underlying
        # the name of the new object...
        Knew = self.signature.ficname+self.strucname
        # ...and make sure that the name is fresh
        while Knew in self.signature.objects:
            Knew = Knew+'*'     
        underlying.add_edges_from([(Knew,K,f) for K in [K for K in self.signature.objects if self.obval[K]]
                                              for f in self.obval[K]])
        relations = [((Knew,self.signature.cod[g[2]],f+g[2]),(Knew,self.signature.cod[g[2]],x))
                     for A in [A for A in self.signature.objects if self.obval[A]]
                     for f in self.obval[A]
                     for g in self.signature.coslice[A]
                     for x in self.obval[self.signature.cod[g[2]]]
                     if self.morval[g].app[f] == x]
        return FiniteInverseCategory(underlying,relations, ficname=self.signature.ficname+'*'+self.strucname)
    
    def Interp(self):
        '''
        Returns a proof-assistant agnostic list of tuples of the form
        (term,type,variable dependencies) to be fed to various interpreters
        '''
        context = []
        for K in [K for K in self.signature.objectsbylevel if self.obval[K]]:
            for x in self.obval[K]:
                context.append((x,K,[self.dep(K,x)[self.signature.mortovar[f][2]] 
                                     for f in self.signature.coslice[K]]))
        return context
    
    def UniMath(self):
        '''
        An interpreter for UniMath.
        '''
        return '\n'.join(['Context ('+''.join(map(str,x[0]))+' : '+''.join(map(str,x[1]))+\
                          ' '+' '.join(map(lambda y: ''.join(map(str,y)),x[2]))+').' 
                          for x in self.Interp()])
    
    def UniMathDataPoint(self,filename='DataPoint'):
        '''
        Produces a Coq file "DataPoint.v" with the interpretation of the fic-structure M
        as a context in UniMath vernacular.
        '''
        # open the file to write
        coqfile = open(filename+'.v', 'w')
        # write the minimum Import requirement
        coqfile.write('Require Import UniMath.Foundations.PartB. \n')
        coqfile.write('\n')    
        coqfile.write('\n')    
        # definition of the context corresponding to the given fic
        LLstring = self.signature.UniMathShape_asContext()
        coqfile.write(LLstring)
        coqfile.write('\n')
        coqfile.write('\n')
        # definition of the L-structure M as a context
        Mstring = self.UniMath()
        coqfile.write(Mstring)

class FICStructureHomomorphism(FICStructure):
    '''
    An L-structure homomorphism between L-structures G and D from a mathematical point of view
    is a natural transformation a : G => D

    The primary interest for including L-homomorphisms in this development is in order to make
    use of natural transformation c:  yK => M for some K in L and some L-structure M, since 
    such natural transformations can be thought of as "columns" in the data shape.
    '''
    def __init__(self,L,M,N, funcdata = None):
        # check if a fic has been provided
        if isinstance(L, FiniteInverseCategory):
            self.signature = L
        else:
            raise ValueError('Did not provide a fic L as input')
        # check that two fic-structures have been provided and that they are defined over 
        # the same fic. 
        if isinstance(M, FICStructure) and isinstance(N,FICStructure):
            if M.signature == N.signature:
                self.ficstruc1 = M
                self.ficstruc2 = N
            else:
                raise ValueError('The L-structures are not defined over the same L')
        else:
            raise ValueError('Did not provide L-structures as input')
        # check that the input data provided is of the right form
        if funcdata is not None:
            if not isinstance(funcdata,dict):
                raise ValueError('The definition of the natural transformation must be '
                                 'given in the form of an {object:function} dict')
            for K in funcdata.keys():
                if K not in self.signature.objects:
                    raise ValueError('The keys of the input dict must be objects in L: ',
                                     K, 'is not an object in L')
                if M.obval[K] != [] and N.obval[K] == []:
                    raise ValueError('There is no natural transformation between the '
                                     'L-structures provided because '+str(M.obval[K])+' is '
                                     ' non-empty but '+str(N.obval[K])+'is empty')
                if not isinstance(funcdata[K],TypedFunction):
                    raise ValueError('The values of the input dict must be TypedFunctions :',
                                     funcdata[K], 'is not a a TypedFunction')
                if funcdata[K].domain != M.obval[K] or funcdata[K].codomain != N.obval[K]:
                    raise ValueError(funcdata[K], 'is not a function MK -> NK')
                # it is unclear, at this point, whether this last test is necessary
                if not funcdata[K].istotal():
                    raise ValueError('Functions must be total')
        else:
            raise ValueError('There is no "canonical" natural transformation - data must be '
                             ' provided.')
        self.funcval = funcdata
        # check the naturality of the given functions
        for K in [K for K in L.objects if M.obval[K]]:
            for f in [f for f in L.morphisms if L.dom[f[2]] == K]:
                Mfa_KK = M.morval[f].compose(funcdata[L.cod[f[2]]])
                #print(L.dom[f[2]],N.morval[f])
                a_KNf = funcdata[L.dom[f[2]]].compose(N.morval[f])
                if not TypedFunction.funextequal(Mfa_KK,a_KNf):
                    raise ValueError('Not a natural transformation: '+str(Mfa_KK)+' '
                                     'and '+str(a_KNf)+' do not commute.')
        
        
    
        
                
        
        
               