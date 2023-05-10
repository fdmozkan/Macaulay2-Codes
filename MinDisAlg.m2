
t0=cpuTime()
needsPackage "NormalToricVarieties"
ring NormalToricVariety := PolynomialRing => (
    cacheValue symbol ring) (
    X -> (
    	if isDegenerate X then 
      	    error "-- not yet implemented for degenerate varieties";
    	if not isFreeModule classGroup X then 
      	    error "-- gradings by torsion groups not yet implemented";
    	-- constructing ring
    	K := X.cache.CoefficientRing;	  
    	x := X.cache.Variable;	  
	r:=#rays X;
    	deg := entries transpose fromWDivToCl X;
    	S := K (monoid [x_1..x_r, Degrees => deg]);
    	S.variety = X;
    	S 
	)
    );
q=7
alpha={0,1}
X=hirzebruchSurface(2, CoefficientRing => GF(q,Variable=>t) )
S=ring X
IY=ideal ((x_3)^(2)-(x_1)^(2),(x_4)^(3)-(x_3)^(2*(3))*x_2^(3))
Balpha=basis(alpha,S/IY)
N=flatten applyTable({apply(toList (set(0..q-1))^**(hilbertFunction(alpha, S/IY))- (set{0})^**(hilbertFunction(alpha, S/IY)),i-> toList i)}, i-> deepSplice  i)
P= apply(#N, j-> vector flatten N_{j} )
D= for i from 0 to #P-1 list Balpha*  flatten P_{i}
A=    flatten for i from 0 to #D-1 list entries  (flatten D_{i})#0
Malpha= apply(A, i->substitute(i,S))  
Z=select(Malpha, f-> not quotient (IY, ideal f)==IY)
T0=cpuTime()

------------------------------------Alg1-------------------
t1=cpuTime()
PrIY=primaryDecomposition IY

delta1=hilbertPolynomial(X,IY)-max apply(Z, f->#select(PrIY, i-> f%i==0))
T1=cpuTime()
T1-t1


------------------------------------------------Alg2-------------------
t2=cpuTime()
PrIY=primaryDecomposition IY

IVXYf=(PrIY,f,S)->(int:= ideal(1_S); scan(PrIY, i-> if f%i==0 then int=intersect(int,i)); int) ; 
Ideals=apply(Z, f->IVXYf(PrIY,f, S))
delta2=hilbertPolynomial(X,IY)-max apply(Ideals, I-> hilbertPolynomial(X,I))
T2=cpuTime()
T2-t2

------------------------------------Alg3-------------------
t3=cpuTime()

deltaTilde=hilbertPolynomial(X,IY)-max apply(Z, f-> hilbertPolynomial(X,IY+ideal (f)))
T3=cpuTime() 
T3-t3

-------------------------------------------------------
T0-t0
T1-t1
T2-t2
T3-t3



TIME=(T0-t0+T1-t1, T0-t0+T2-t2, T0-t0+T3-t3)
DELTA=(delta1, delta2, deltaTilde) 






