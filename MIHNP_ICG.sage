#This code is for MIHNP  using our approach.  For our lattice generation, set Sublattice = 0.  
#To run this code please install Python 3.8 and Sage 9.3 
#For MIHNP, set MIHNP = 1. For ICG, set MIHNP = 0

Sublattice = 1
MIHNP = 0


def MIHNP_CREATION(): #Generation of MIHNP
       
    a = ZZ.random_element(P) #a is the secret. Attacker tries to find it.
    X = []
    B = []
    E = []
    for i in range(n+1):
        xi = ZZ.random_element(P)
        X.append(xi)
        yi = (a+xi).inverse_mod(P)
        bi = yi-yi%2^unknown #bi is known to the attacker
        ei = yi%2^unknown    #ci is unknown to the attacker
        B.append(bi)
        E.append(ei)
        
    #G contains all modular polynomials. Attacker tries to find the root of these polynomials	
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

    return G, E


def ICG_CREATION(): #Generation of ICG
    a = ZZ.random_element(P)
    b = ZZ.random_element(P)
    X = []
    B = []		
    E = []
    v1 = ZZ.random_element(P)
    X.append(v1)

    for i in range(n+1):
        vi = a*((X[i]).inverse_mod(P))+b
        vi = vi%P
        X.append(vi)
    for i in range(n+1):
        vi=X[i]	
        bi=vi-vi%2^unknown
        ei=vi%2^unknown
        B.append(bi)
        E.append(ei)

    K=[0]
    for i in range(1,n):
         ki = a*((K[i-1]+b).inverse_mod(P))
         ki = ki%P
         K.append(ki)

    G=[]
    for j in range(n):
         a0i = -K[j]*B[0] - b*B[0] + K[j]*B[j+1] + B[0]*B[j+1] - a
         a0i = a0i%P
         b0i = -b - K[j] + B[j+1]
         c0i = B[0] + K[j]
         g = Z[0]*Z[j+1] + (b0i)%P*Z[0] + (c0i)%P*Z[j+1] + a0i
         G.append(g)
                        

    return G, E      


def POLYNOMIALS_FOR_LATTICE_GENERATION(G): #Polynomials for lattice generation starts here. We will store these in an array F
    I = []
    for i0 in range(d+1):
        for i in range(2^n):
            B = ZZ(i).digits(base = 2, padto = n)
            A = [B[j] for j in range(n)]            
            A.append(i0)
            A.reverse()
            
            
            summation = sum(A[j] for j in range(1, n+1))
            
            if(summation <= d):
                I.append(A)
    for i0 in range(t+1):
        for i in range(2^n):
          
            B = ZZ(i).digits(base = 2, padto = n)
            A = [B[j] for j in range(n)]            
            A.append(i0)
            A.reverse()
            
            summation = sum(A[j] for j in range(1, n+1))
            
            if(summation == d+1):
                I.append(A)
    M = []
    for i in range(len(I)):
        ss = prod(Z[j]^(I[i][j]) for j in range(n+1))
        M.append(ss)
    ZERO = [0]*(n+1)
    
        
    F = []
         
    for i in range(len(M)):
        ss = M[i]
        S = list((M[i]).exponents()[0])
        s = sum (S[j] for j in range(1,n+1))
        
        if(s == 0):
            F.append(M[i]*P^d)
        else:
            if(S[0] >= s):

                f = prod((G[j])^S[j+1] for j in range(n))
                f = f * Z[0]^(S[0]-s)
                
                S2 = f.monomials()
                cf = f.coefficients()
                g = sum((cf[j]%P^(s))*S2[j] for j in range(len(S2))) 
               
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
                    ss = prod(Z[k]^(S[k]) for k in range(1,n+1))
                    ss = ss*Z[0]^j
                    
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
                    f = sum(ZZ(MSIN[l][j])*F4[j] for j in range(s))
                
                    
                    S2 = f.monomials()
                    cf = f.coefficients()
                    g = sum((cf[j]%P^(s-1))*S2[j] for j in range(len(S2)))  
                    
                    F.append(g*P^(d+1-s))
                else:
                    F.append(F4[j]*P^d)



    return F, I, ZERO          


def POLYNOMIALS_FOR_SUBLATTICE_GENERATION(F,I,ZERO): 
    I1  =  []
    for i in range(2^n):
            for i0 in range(d):
                
                C  =  ZZ(i).digits(base  =  2, padto  =  n)

                A = [C[j] for j in range(n)]            
                A.append(i0)
                A.reverse()
                
                
                summation = sum(A[j] for j in range(1, n+1))
                if(summation <=  d):
                    I1.append(A)
           
    I3  =  []
    for i in range(2^n):
            for i0 in range(t+1):
                
                C  =  ZZ(i).digits(base  =  2, padto  =  n)
                A = [C[j] for j in range(n)]            
                A.append(i0)
                A.reverse()
                
                summation = sum(A[j] for j in range(1, n+1))
                if(summation  ==  d+1):
                    I3.append(A)

    MM = []
    for i in range(len(I3)):
            ss = prod(Z[j]^(I3[i][j]) for j in range(n+1))
            MM.append(ss)




    F_Tilde = []

    for i in range(len(I)):
            if(I[i] in I1):
                F_Tilde.append(F[i])
        

    for i1 in range(len(I3)):

            S = list((MM[i1]).exponents()[0])

            s = sum(S[j] for j in range(1, n+1))


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
                ss = prod(Z[k]^(S[k]) for k in range(1,n+1))
                ss = ss*Z[0]^j
                
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
            f = sum(ZZ(MSIN[l][j])*F4[j] for j in range(s))
            

            S2 = f.monomials()
            
            cf = f.coefficients()
            g = sum((cf[j]%P^(s-1))*S2[j] for j in range(len(S2)))   

            


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
                g = g + f


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

                
    #We store modified polynomials in F
    F=[]
    for i in range(len(F_Tilde)):
            F.append(F_Tilde[i])
   
    return F






PARA = [[3,2,1], [6,1,0], [4,2,0], [4,2,1], [5,2,0], [5,2,1], [6,2,0], [6,2,1], [7,2,0], [7,2,1], [8,2,0], [6,3,0], [9,2,0], [10,2,0]]

KNOWN = [595,585,560,550,530,525,505,505,495,490,475,485,460,450]

P = ZZ.random_element(2^999,2^1000)
P = next_prime(P)

for par in range(13):
    success = 0
    
    known = KNOWN[par] #Known part of the secret from MSB side
    unknown = 1000-known #Unknown part from LSB side
    n = PARA[par][0]
    d = PARA[par][1]
    t = PARA[par][2]
    R = PolynomialRing(QQ, n+1, 'x', order = 'invlex')
    Z  =  list(R.gens())
    if(MIHNP == 1):
       G, E = MIHNP_CREATION()
    else:
       G, E = ICG_CREATION()
  

    F, I, ZERO = POLYNOMIALS_FOR_LATTICE_GENERATION(G)

    if(Sublattice == 1):
       F = POLYNOMIALS_FOR_SUBLATTICE_GENERATION(F,I,ZERO)
    
    
    """
    We rearrange polynomials and monomials in such a way that the corresponding generated matrix is lower triangular.  
    Store polynomials in F_Final and monomials in  LD_MON. Leading terms are in LD_MON.    
    """   
 
    LD_MON = []
    SS = []
    S1 = []
    F_Final = []
    for _ in range(10):
        for i in range(len(F)):
            S2 = (F[i]).monomials()
            SS = union(SS,S2)
            S2 = Set(S2).difference(Set(S1))
            if(len(S2) == 1):
                LD_MON.append(S2[0])
                S1=union(S1, LD_MON)
                F_Final.append(F[i])


        
    

    
    #*********************************************
    Dimension = len(F)
    if(Sublattice == 0 and MIHNP ==0):
        print('ICG: Lattice Dimension = ', Dimension)
        print('Parameters are', n,d,t)
    if(Sublattice == 0 and MIHNP ==1):
        print('MIHNP: Lattice Dimension = ', Dimension)
        print('Parameters are', n,d,t)
    
    if(Sublattice == 1 and MIHNP == 0):
        print('ICG: Sublattice Dimension = ', Dimension)
        print('Parameters are', n,d,t)

    if(Sublattice == 1 and MIHNP == 1):
        print('MIHNP: Sublattice Dimension = ', Dimension)
        print('Parameters are', n,d,t)
    
    #Upper bound of the root
    U =   2^unknown
    PT1 = []
    PT2 = []
    for i in range(n+1):
        PT1.append(Z[i]*U)
        PT2.append(U)

    #M2 is the matrix corresponding to shift polynomials
    M2 = zero_matrix(ZZ,Dimension)
    for i in range(Dimension):
        f = F_Final[i]
        g=0
        for j in range(len(LD_MON)):
            cij = f.coefficient(LD_MON[j])
            cij = cij(ZERO)
            if(cij > P^d):
                cij = cij%P^d 
            g = g+cij*LD_MON[j]

        f = g(PT1)
        for j in range(len(LD_MON)):
            cij = f.coefficient(LD_MON[j])
            cij = cij(ZERO)
                    
            M2[i,j] = cij

        
    from time import process_time
    TIME_Start = process_time()
    M2 = M2.LLL()
    TIME_Stop = process_time()
    lll = TIME_Stop - TIME_Start

    #Store those polynomials which are zero over integers in POLY_SET
    POLY_SET = []


    for j in range(Dimension):
        f1 = 0
        for i in range(Dimension):
            f1 = f1+ZZ(M2[j][i]/LD_MON[i](PT2))*LD_MON[i]
        if(f1(E) == 0):
            POLY_SET.append(f1)
              
              
        else:
            break



       
    """
    Consider the polynomials of POLY_SET as modular polynomials over GF(p) for some small primes p and calculate Grobner basis 
    """ 


    Rz = PolynomialRing(ZZ, n+1, 'X')
    Z  =  list(Rz.gens())
    M4 = []
    for i in range(len(POLY_SET)):
        f = (POLY_SET[i])(Z)
        M4.append(f)
    CRT = []
    gb = 0
    PRIME_SET = [] 
    j = 0
    PROD_PRIME = 1
    for i in range(1000):
        if(is_prime(i) == True):
            PROD_PRIME = PROD_PRIME*i
            PRIME_SET.append(i)
            j = j+1
        if(PROD_PRIME>2*U):
            break

    for j in range(len(PRIME_SET)):
        PP = PRIME_SET[ZZ(j)]
        R = PolynomialRing(GF(PP), n+1, 'X')
        M5 = []
        for i in range(len(M4)):
            g = R(M4[i])
            M5.append(g)
        I = (M5)*R
             
        from time import process_time
        TIME_Start = process_time()
        GB = I.groebner_basis()
        TIME_Stop = process_time()
        gb =  gb + TIME_Stop - TIME_Start
        CRT.append(ZZ(-GB[0](ZERO)))

        
    CRT = list(CRT)
    PRIME_SET = list(PRIME_SET)
    X = crt(CRT,PRIME_SET) #Use Chinese Remainder Theorem
    j = 0
    for i in range(n+1):
        if(X == E[i]):
            j = 1
              
    if(j == 1):
        success = success + 1
    print('LLL time ',round(lll,2),'\t','GB time',round(gb,2),'\t','#Success',success)
    print('---------------------------------------\n')



