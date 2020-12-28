#  experiments of Gentry-Szydlo averaging attack
#  the avergating term is alpha_i/alpha_j

n=4    # 2x the degree of cyclotomic polynomial
B=100    # bound for "small"
Big=14  # bound for "big"
Bound_secret = 1  # bound for "big"


print "secret Bound =", Bound_secret, "small Bound =", B, "Big bound =", B, "n=", n

#G = K.galois_group(); G

K.<x>=CyclotomicField(2*n)
OK = K.ring_of_integers()
R = ZZ["x"]
f = R.gen()**n + 1

#KK.<z>, L = K.subfield(x^2)
#print KK

#Kc=K.complex_conjugation()
#print Kc

def randVecOK(l):
    return Matrix(OK,[OK.random_element(x=-B,y=B+1) for i in range(l)])

def randMatOK(l):
    return Matrix(OK,[[OK.random_element(x=-B,y=B+1) for i in range(l)] for j in range(l)])

def toy_examples():
    """ inverse, norm ,.... in R or K """
    """ Z[z_n] is Euclidean iff n \in {1, 3, 4, 5, 7, 8, 9, 11, 12, 13, 15, 16, 17, 19, 20, 21, 24, 25, 27, 28, 32, 33, 35, 36, 40, 44, 45, 48, 60, 84 } """
    print "generating random elements f and g"
    f = OK.random_element(x=-B,y=B+1)
    g = OK.random_element(x=-B,y=B+1)
    #units = K.S_units([])
    #print units
    #print units[2]*units[2]

    invf, invg = 1/f, 1/g
    MF, MG = f.matrix(), g.matrix()
    charMF, charMG = MF.charpoly(), MG.charpoly()
    MFinv = 1/MF
    print "f=", f, "\n trace of f", f.trace(), "\n norm of f", f.norm(), "\n 1/f=", invf
    #print "fu=", f*units[1]
    print "g=", g, "\n norm of g", g.norm(), "\n 1/g=", invg
    print "MF=", MF, "\n 1/f=", invf.matrix()
    #print "MF eigenvalues", MF.eigenvalues()
    #print "MF eigenvectors", MF.eigenmatrix_right()
    #print "MG=", MG, "\n 1/g=", invg.matrix()

    fdg = f*invg
    Mfdg = fdg.matrix()
    print "f/g:", fdg
    print "g.norm() * f/g:", OK(g.norm()*fdg)
    I = OK.ideal([f])
    IJ = OK.ideal(OK(g.norm()*fdg))
    print "I = OK.ideal([f])", I.norm(), I
    print "I.is_principal()", I.is_principal()
    print IJ.norm(), IJ
    print IJ.is_principal()
#toy_examples()

def directavg():
    """ test whether 1/aj converges, without worrying about conjuagation.  """

    C = 100
    aj = [1/OK.random_element(x=-B,y=B+1) for i in range(C)]
    #aj = [float( (OK.random_element(x=-B,y=B+1)/OK.random_element(x=-B,y=B+1)).list()[0] ) for i in range(C)]
    summ = sum(aj)
    #print summ/C
    for i in range(4):
        print float(summ.list()[i])/C

directavg()
