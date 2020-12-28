# toy examples for number fields
# small scale experiments on GGH13/GGH15 cryptanalysis
# trying to verify that alpha_i/alpha_j are the solutions for a systems of non-linear equations.
# also included experiments of Gentry-Szydlo averaging attack

n=8    # 2x the degree of cyclotomic polynomial
d=2     # dimension of the matrix in 
B=25    # bound for "small"
Big=10  # bound for small but slightly bigger things
q=200

sigma = n
sigma_p = round(n**(ZZ(5)/2) * sigma)
sigma_s = round(n**(ZZ(3)/2) * sigma_p**2)

print "q=",q, "B=", B, "n=", n

#G = K.galois_group(); G

K.<x>=CyclotomicField(2*n)
OK = K.ring_of_integers()
R = ZZ["x"]
Rq = R.change_ring(IntegerModRing(q))
f = R.gen()**n + 1
Rqf=Rq.quotient_ring(Rq.ideal(f))

KK.<z>, L = K.subfield(x^2)
print KK

Kc=K.complex_conjugation()
print Kc

def randVecOK(l):
    return Matrix(OK,[OK.random_element(x=-B,y=B+1) for i in range(l)])

def randMatOK(l):
    return Matrix(OK,[[OK.random_element(x=-B,y=B+1) for i in range(l)] for j in range(l)])

def toy_examples():
    """ inverse, norm ,.... in R or K """
    """ Z[z_n] is Euclidean iff n \in {1, 3, 4, 5, 7, 8, 9, 11, 12, 13, 15, 16, 17, 19, 20, 21, 24, 25, 27, 28, 32, 33, 35, 36, 40, 44, 45, 48, 60, 84 } """
    f = OK.random_element(x=-B,y=B+1)
    g = OK.random_element(x=-B,y=B+1)
    h = OK.random_element(x=-B,y=B+1)
    i = OK.random_element(x=-B,y=B+1)
    units = K.S_units([])
    print units
    #print units[2]*units[2]

    invf = 1/f
    invg = 1/g
    #MF = f.matrix()
    #MG = g.matrix()
    #charMF = MF.charpoly()
    #charMG = MG.charpoly()
    #MFinv = 1/MF
    print "f=", f, "\n trace of f", f.trace(), "\n norm of f", f.norm(), "\n 1/f=", invf
    #print "fu=", f*units[1]
    #print "fuu=", f*units[2]*units[2]*units[2]*units[2]
    print "g=", g, "\n norm of g", g.norm(), "\n 1/g=", invg
    #print "MF=", MF, "\n 1/f=", invf.matrix()
    #print "MF eigenvalues", MF.eigenvalues()
    #print "MF eigenvectors", MF.eigenmatrix_right()
    #print "MG=", MG, "\n 1/g=", invg.matrix()

    #fdg = f*invg
    #Mfdg = fdg.matrix()
    #print fdg
    #print OK(g.norm()*fdg)
    #I = OK.ideal([f])
    #IJ = OK.ideal(OK(g.norm()*fdg))
    #print I.norm(), I
    #print I.is_principal()
    #print IJ.norm(), IJ
    #print IJ.is_principal()
#    print "h=", h, "\ng=",g, "\nf=",f, "\nfh=",f*h
#    z = gcd(f*h, g*h)
#    print z
#    print z/h
toy_examples()


def toy_examples2():
    f = [OK.random_element(x=-B,y=B+1) for i in range(4)]
    for i in f:
        print "f=",i,"f.trace ", i.norm()
        print i.matrix()
    print "f[0]*f[1]=", f[0]*f[1], (f[0]*f[1]).norm()
#toy_examples2()


def matrix_kernel_experiments():
    a1 = randMatOK(d);
    a2 = randMatOK(d);
    print "a1=",a1, "\n a2=",a2
    # now build equations out of them
    N = block_matrix([[a1],[a1]]);
    print N, "\n rank of N:", N.rank()
    print "kernel of N:", kernel(N)
    #KN = kernel(N).matrix()

    
def matrix_kernel_alpha_cross_product_e0():
    """ a small scale experiment showing that the cross product of 2C elements can be digged out from the kernel, with e=0"""
    C=3
    print "we set C=",C 
    a2p=[OK.random_element(x=-B,y=B+1) for i in range(2*C)]
    # M is the cross product
    print a2p
    print [wrw.norm() for wrw in a2p]
    M = [Matrix(K,[a2p[i]*a2p[2+j]*a2p[4+k] ]) for i in range(2) for j in range(2) for k in range(2)]
    print "M=", M
    print "W simulates the matrix obtained by collecting different paths"
    # W = M^T
    W = block_matrix([ [i] for i in M ]);
    print "W=",W, "\n rank of W:", W.rank()
    print "kernel of W:", kernel(W)
    p = kernel(W).matrix()
    print "In the simplified mode we can directlt read the ratios from p, e.g. when C=3:"
    print "alpha_{3,0}/alpha_{3,1}=",a2p[4]/a2p[5]
    print "p_{7,8}/p_{7,7}=",p[6][7]/p[6][6]
    print "it's also easy to verify that P_{1,8}*P_{4,8}-P_{2,8}*P_{3,8}=0"
    print p[0][7]*p[3][7]
    print p[1][7]*p[2][7]
    print "need more for real experiments when e>0 (in the real cryptanalysis e=2m+3)"

def matrix_kernel_alpha_cross_product_emore():
    """ a small scale experiment showing that the cross product of 2C elements can be digged out from the kernel, with e=1"""
    C=3
    print "we set C=",C 
    a2p =[OK.random_element(x=-B,y=B+1) for i in range(2*C)]
    # M is the cross product
    print a2p
    M = [Matrix(K,[a2p[i]*a2p[2+j]*a2p[4+k]]) for i in range(2) for j in range(2) for k in range(2)]
    print "M=", M
    print "W simulates the matrix obtained by collecting different paths"
    # W = M^T
    W = block_matrix([ [i, K(OK.random_element(x=-B,y=B+1))] for i in M ]);
    print "W=",W, "\n rank of W:", W.rank()
    print "kernel of W:", kernel(W)
    p = kernel(W).matrix()
    print "first we verify"
    print p[0][6]*p[3][6]*a2p[4]*a2p[4] + (p[0][6]*p[3][7] + p[0][7]*p[3][6])*a2p[4]*a2p[5] + p[0][7]*p[3][7]*a2p[5]*a2p[5]
    print p[1][6]*p[2][6]*a2p[4]*a2p[4] + (p[1][6]*p[2][7] + p[1][7]*p[2][6])*a2p[4]*a2p[5] + p[1][7]*p[2][7]*a2p[5]*a2p[5]
    print p[0][6]*p[3][6]-p[1][6]*p[2][6], (p[0][6]*p[3][7] + p[0][7]*p[3][6])-(p[1][6]*p[2][7] + p[1][7]*p[2][6]), p[0][7]*p[3][7]-p[1][7]*p[2][7]
    
    print p[0][6]*p[5][6]*a2p[4]*a2p[4] + (p[0][6]*p[5][7] + p[0][7]*p[5][6])*a2p[4]*a2p[5] + p[0][7]*p[5][7]*a2p[5]*a2p[5]
    print p[1][6]*p[4][6]*a2p[4]*a2p[4] + (p[1][6]*p[4][7] + p[1][7]*p[4][6])*a2p[4]*a2p[5] + p[1][7]*p[4][7]*a2p[5]*a2p[5]
    print p[0][6]*p[5][6]-p[1][6]*p[4][6], (p[0][6]*p[5][7] + p[0][7]*p[5][6])-(p[1][6]*p[4][7] + p[1][7]*p[4][6]), p[0][7]*p[5][7]-p[1][7]*p[4][7]

    print p[2][6]*p[5][6]*a2p[4]*a2p[4] + (p[2][6]*p[5][7] + p[2][7]*p[5][6])*a2p[4]*a2p[5] + p[2][7]*p[5][7]*a2p[5]*a2p[5]
    print p[3][6]*p[4][6]*a2p[4]*a2p[4] + (p[3][6]*p[4][7] + p[3][7]*p[4][6])*a2p[4]*a2p[5] + p[3][7]*p[4][7]*a2p[5]*a2p[5]
    print p[2][6]*p[5][6]-p[3][6]*p[4][6], (p[2][6]*p[5][7] + p[2][7]*p[5][6])-(p[3][6]*p[4][7] + p[3][7]*p[4][6]), p[2][7]*p[5][7]-p[3][7]*p[4][7]
    
    F=Matrix(K,[[p[0][6]*p[3][6]-p[1][6]*p[2][6], (p[0][6]*p[3][7] + p[0][7]*p[3][6])-(p[1][6]*p[2][7] + p[1][7]*p[2][6]), p[0][7]*p[3][7]-p[1][7]*p[2][7]],
               [p[0][6]*p[5][6]-p[1][6]*p[4][6], (p[0][6]*p[5][7] + p[0][7]*p[5][6])-(p[1][6]*p[4][7] + p[1][7]*p[4][6]), p[0][7]*p[5][7]-p[1][7]*p[4][7]],
               [p[2][6]*p[5][6]-p[3][6]*p[4][6], (p[2][6]*p[5][7] + p[2][7]*p[5][6])-(p[3][6]*p[4][7] + p[3][7]*p[4][6]), p[2][7]*p[5][7]-p[3][7]*p[4][7]]])
    print F, F.transpose().kernel()
    #print "alpha_{3,0}/alpha_{3,1}=",a2p[4]/a2p[5]
    print "alpha_{3,1}/alpha_{3,0}=",a2p[5]/a2p[4]
    
    print a2p[5].norm(KK)

#matrix_kernel_alpha_cross_product_emore()
