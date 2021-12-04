#Set Sub_Lattice  =  1 for Sublattice generation

#SET MIHNP = 1 for MIHNP & set MIHNP = 0 for ICG
MIHNP = 0

Sub_Lattice  =  1


PARA = [[3,2,1],[6,1,0],[4,2,0],[4,2,1],[5,2,0],[5,2,1],[6,2,0],[6,2,1],[7,2,0], [7,2,1],[8,2,0],[6,3,0],[9,2,0],[10,2,0]]

KNOWN = [595,585,560,550,530,525,505,505,495,490,475,485,460,450]

P = ZZ.random_element(2^999,2^1000)
P = next_prime(P)
for par in range(10):
        suc = 0
        
        known = KNOWN[par]
        unknown = 1000-known
        ss = 1
        PRIME = []
        j = 0
        for i in range(1000):
	 if(is_prime(i) == True):
	    ss = ss*i
	    PRIME.append(i)
	    j = j+1
         if(ss>2^(unknown+5)):
	    break
        n = PARA[par][0]
	d = PARA[par][1]
	t = PARA[par][2]
        R = PolynomialRing(QQ, n+1, 'x', order = 'invlex')
	Z  =  list(R.gens())
        
        
        if(MIHNP == 1):
		a = ZZ.random_element(P)
		X = []
		B = []
		E = []
		for i in range(n+1):
	    		xi = ZZ.random_element(P)
	    		X.append(xi)
	    		yi = (a+xi).inverse_mod(P)
	    		bi = yi-yi%2^unknown
	    		ei = yi%2^unknown
	    		B.append(bi)
	    		E.append(ei)
		
		G = []
		for j in range(1,n+1):
	    		Aj = X[0]-X[j]
	    		Bj = X[0]*B[j]-X[j]*B[j]+1
	    		Cj = X[0]*B[0]-X[j]*B[0]-1
	    		Dj = (X[0]-X[j])*B[0]*B[j]+B[0]-B[j]
	    		f = Aj*Z[0]*Z[j]+Bj*Z[0]+Cj*Z[j]+Dj
	    		b = (Aj).inverse_mod(P)
	    		g = Z[0]*Z[j]+(Bj*b)%P*Z[0]+(Cj*b)%P*Z[j]+(Dj*b)%P
	    		G.append(g)


        if(MIHNP == 0):
                
		a=ZZ.random_element(P)
		b=ZZ.random_element(P)
		X=[]
		B=[]
		E=[]
		v1=ZZ.random_element(P)
	    	X.append(v1)
                for i in range(n+1):
	    	    vi=a*((X[i]).inverse_mod(P))+b
		    vi=vi%P
		    X.append(vi)
	    	for i in range(n+1):
		    vi=X[i]	
		    bi=vi-vi%2^unknown
	    	    ei=vi%2^unknown
	    	    B.append(bi)
	    	    E.append(ei)
		    
		K=[0]
		for i in range(1,n):
		    ki=a*((K[i-1]+b).inverse_mod(P))
		    ki=ki%P
		    K.append(ki)
		
		G=[]
		for j in range(n):
	    	    a0i=-K[j]*B[0] - b*B[0] + K[j]*B[j+1] + B[0]*B[j+1] - a
		    a0i=a0i%P
	    	    b0i=-b-K[j]+B[j+1]
	    	    c0i=B[0]+K[j]
		    g=Z[0]*Z[j+1]+(b0i)%P*Z[0]+(c0i)%P*Z[j+1]+a0i
		    G.append(g)



	I = []
	for i0 in range(d+1):
	    for i in range(2^n):
		A = [i0]
		B = ZZ(i).digits(base = 2, padto = n)
		j = n-1
		while(j >= 0):
		    A.append(B[j])
		    j = j-1
		sum = 0
		for j in range(1,n+1):
  		    sum = sum+A[j]
		if(sum <= d):
 		    I.append(A)
	for i0 in range(t+1):
	    for i in range(2^n):
		A = [i0]
		B = ZZ(i).digits(base = 2, padto = n)
		j = n-1
		while(j >= 0):
  		    A.append(B[j])
  		    j = j-1
		sum = 0
		for j in range(1,n+1):
  		    sum = sum+A[j]
		if(sum == d+1):
  		    I.append(A)
        M = []
	for i in range(len(I)):
	    ss = 1
	    for j in range(n+1):
	       	ss = ss*Z[j]^(I[i][j])
	    M.append(ss)
        ZERO = []
	for i in range(n+1):
	    ZERO.append(0)
        

        F = []
         
	for i in range(len(M)):
	    ss = M[i]
	    S = list((M[i]).exponents()[0])
	    s = 0
	    for j in range(1,n+1):
	      	s = s+S[j]
	    if(s == 0):
		F.append(M[i]*P^d)
	    else:
		if(S[0] >= s):
		    f = Z[0]^(S[0]-s)
		    for j in range(n):
			f = f*(G[j])^S[j+1]
		    S2 = f.monomials()
		    g = 0
		    cf = f.coefficients()
		    for j in range(len(S2)):
			cf[j] = cf[j]%P^(s)
			cf[j] = ZZ(cf[j])
			g = g+cf[j]*S2[j]
		    F.append(g*P^(d-s))
		else:
    		    F2 = []
    		    F3 = []
    		    F4 = []
    		    for j in range(1,n+1):
    			if(S[j] == 1):
        		    F2.append(Z[j])
        		    F3.append(G[j-1])
		    for j in range(len(F2)):
        		f = 1
        		for k in range(len(F2)):
            		    if(k == j):
                		f = f*F2[j]
            		    else:
                		f = f*F3[k]
        		F4.append(f)
    		    F1 = []
    		    for j in range(s):
        		ss = Z[0]^j
        		for k in range(1,n+1):
              			ss = ss*(Z[k])^S[k]
        		F1.append(ss)
		    if(s>1):
			R1 = IntegerModRing(P^(s-1))
			MS = zero_matrix(R1,s)
			for j in range(s):
			    for l in range(s):
				cjl = (F4[j]).coefficient(F1[l])
				cjl = cjl(ZERO)
				MS[j,l] = cjl
			MSIN = MS.inverse()
			l = S[0]
			f = 0
			for j in range(s):
			    f = f+ZZ(MSIN[l][j])*F4[j]
			S2 = f.monomials()
			g = 0
			cf = f.coefficients()
			for j in range(len(S2)):
			    cf[j] = cf[j]%P^(s-1)
			    g = g+cf[j]*S2[j]
			F.append(g*P^(d+1-s))
		    else:
			F.append(F4[j]*P^d)



        


        #*********************************************





                   
        if(Sub_Lattice  ==  1):


		I1  =  []
		for i in range(2^n):
		 for i0 in range(d):
		      A  =  [i0]
		      C  =  ZZ(i).digits(base  =  2, padto  =  n)
		      j  =  0
		      while(j <=  n-1):
		           A.append(C[j])
		           j  =  j+1
		      sum  =  0
		      for j in range(1,n+1):
		           sum  =  sum+A[j]
		      if(sum <=  d):
		           I1.append(A)
	       
		I3  =  []
		for i in range(2^n):
		 for i0 in range(t+1):
		      A  =  [i0]
		      C  =  ZZ(i).digits(base  =  2, padto  =  n)
		      j  =  0
		      while(j <=  n-1):
		           A.append(C[j])
		           j  =  j+1
		      sum  =  0
		      for j in range(1,n+1):
		           sum  =  sum+A[j]
		      if(sum  ==  d+1):
		           I3.append(A)

		MM = []
		for i in range(len(I3)):
		    ss = 1
		    for j in range(n+1):
		       	ss = ss*Z[j]^(I3[i][j])
		    MM.append(ss)




		F_Tilde = []

		for i in range(len(I)):
		     if(I[i] in I1):
		       F_Tilde.append(F[i])

		

		for i1 in range(len(I3)):

		   S = list((MM[i1]).exponents()[0])

		   s = 0
		   for j in range(1,n+1):
		      	s = s+S[j]

		   
	     
		   F2 = []
	    	   F3 = []
	    	   F4 = []
	    	   for j in range(1,n+1):
	    			if(S[j] == 1):
				    F2.append(Z[j])
				    F3.append(G[j-1])
		   for j in range(len(F2)):
				f = 1
				for k in range(len(F2)):
		    		    if(k == j):
		        		f = f*F2[j]
		    		    else:
		        		f = f*F3[k]
				F4.append(f)
		   

		   F1 = []
		   for j in range(s):
				ss = Z[0]^j
				for k in range(1,n+1):
		      			ss = ss*(Z[k])^S[k]
				F1.append(ss)
		   R1 = IntegerModRing(P^(s-1))
		   MS = zero_matrix(R1,s)
		   for j in range(s):
				    for l in range(s):
					cjl = (F4[j]).coefficient(F1[l])
					cjl = cjl(ZERO)
					MS[j,l] = cjl

		   MSIN = MS.inverse()
		   x0 = Z[0]
		   l = S[0]
		   f = 0
		   for j in range(s):
			f = f+ZZ(MSIN[l][j])*F4[j]
		   S2 = f.monomials()
		   g = 0
		   cf = f.coefficients()
		   for j in range(len(S2)):
			cf[j] = cf[j]%P^(s-1)
			g = g+cf[j]*S2[j]

		   
	 
		   
		   f1  =  0
		   for j in range(len(F2)):
				f = ZZ(MSIN[l,j])
				for k in range(len(F2)):
		    		    if(k == j):
		                        ci = (F3[k]).coefficient(x0)
		                        ci = ci(ZERO)
		                        ci = ZZ(ci)
		        		f = f*ci
		    		    else:
		        		f = f*F3[k]
		                g = g+f


		   temp  =  0
		   g_monomials  =  g.monomials()
		   for u in range(len(g_monomials)):
		      cu  =  g.coefficient(g_monomials[u])
		      cu  =  cu(ZERO)
		      cu  =  ZZ(cu)
		      cu  =  cu%P^d
		      cu  =  ZZ(cu)
		      temp  =  temp+cu*g_monomials[u]

		   g  =  temp

		   F_Tilde.append(g)

                F=[]
                for i in range(len(F_Tilde)):
                    F.append(F_Tilde[i])

          
        M = []
        SS = []
        S1 = []
        F_Final = []
        for _ in range(10):
          for i in range(len(F)):
            S2 = (F[i]).monomials()
            SS = union(SS,S2)
            S2 = Set(S2).difference(Set(S1))
            if(len(S2) == 1):
               M.append(S2[0])
               S1=union(S1,M)
               F_Final.append(F[i])
               

            
        

        
        #*********************************************
	rr = len(F)
	if(Sub_Lattice == 0):
	    print 'Lattice Dimension = ', rr, len(M)
	    print 'parameters are', n,d,t

	if(Sub_Lattice == 1):
	    print 'Sublattice Dimension = ', rr
	    print 'parameters are', n,d,t
	U = ZZ.random_element(2^(unknown-1), 2^(unknown))
	PT1 = []
	PT2 = []
	for i in range(n+1):
	    PT1.append(Z[i]*U)
	    PT2.append(U)
	M2 = Matrix(ZZ,rr,rr,range(rr*rr))
	for i in range(rr):
	    f = F_Final[i]
            g=0
            for j in range(len(M)):
		cij = f.coefficient(M[j])
		cij = cij(ZERO)
                if(cij > P^d):
                   cij = cij%P^d 
                g = g+cij*M[j]

	    f = g(PT1)
	    for j in range(len(M)):
		cij = f.coefficient(M[j])
		cij = cij(ZERO)
                
		M2[i,j] = cij

        
	tlll = cputime()
        M2 = M2.LLL()
	lll = cputime(tlll)
	VALUE = []
        for i in range(n+1):
	    VALUE.append(E[i])
	M3 = []
	for j in range(rr):
	    f1 = 0
	    for i in range(rr):
		f1 = f1+ZZ(M2[j][i]/M[i](PT2))*M[i]
            if(f1(E) == 0):
	      M3.append(f1)
              
            else:
              break
	Rz = PolynomialRing(ZZ, n+1, 'X')
	Z  =  list(Rz.gens())
	M4 = []
        for i in range(len(M3)):
	    f = (M3[i])(Z)
	    M4.append(f)
	CRT = []
        gb = 0
        for j in range(len(PRIME)):
	    PP = PRIME[ZZ(j)]
	    R = PolynomialRing(GF(PP), n+1, 'X')
	    M5 = []
            for i in range(len(M4)):
		g = R(M4[i])
		M5.append(g)
	    I = (M5)*R
	    t_gb = cputime()
	    GB = I.groebner_basis()
            gb = gb+ cputime(t_gb)
	    CRT.append(ZZ(-GB[0](ZERO)))

        
	CRT = list(CRT)
	PRIME = list(PRIME)
        X = crt(CRT,PRIME)
        j = 0
        for i in range(n+1):
            if(X == E[i]):
                  j = 1
                  #break
        if(j == 1):
            suc = suc+1
        print  'LLL ',round(lll,2),'\t','GB',round(gb,2),'\t','Suc',suc
        print '---------------------------------------\n',

