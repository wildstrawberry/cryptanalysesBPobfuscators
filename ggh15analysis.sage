"""
Cryptanalysis of GGH15 for branching program step pattern XZXZ.
A proof-of-concept implementation of the rank attack.

Setting of the attack: we assume u=xz is a zero input.
The functional branch can be written as
w(x,z) = Sx1 Sz1 Sx2 Ez2 + Sx1 Sz1 Ex2 Dz2 + Sx1 Ez1 Dx2 Dz2 + Ex1 Dz1 Dx2 Dz2

We make the following simplification:
1. Assume the D matrices are also from random instead of sampling from discrete Gaussian.
2. No dummy branch, assume the function evaluates to zero by default.

It can be used to distinguish the following 2 branching programs:
mode 0: every branch is an identity matrix.  Expected rank when r=1: m^3+2*m^2+2*m+2
mode 1: where P is some w-cycle. It still computes all-identity function. Expected rank when r=1: m^3+2*m^2+2*m+4
 I, I, I   , I
 P, P, P^-1, P^-1
--------------------
 X  Z  X     Z

Changelog:
Apr 2018: first publication

"""

R = ZZ  # the base ring

r=1         # the dimension of padded random entries will be 2r, in GGH15 r=1
w=4         # the dimension of permutation matrices, minimum 5 for Barrington but 2 is enough for demonstrate the attack
m=5         # the width of A matrix (so as the ones for E and D)
rho = 2*r+w+m

print "The dimension of padded random entries 2*r:", 2*r
print "The dimension of Barrington matrices w:", w
print "The dimension (width) of A matrix (so as the ones for E and D) m:", m

Jrow = 1          # dimensions of J, the left bookend
Jcol = 2*r+w      # dimensions of J, the left bookend
Wrow = m^3+m^2+m+5 # dimension of W needed to be accumulated
Wcol = m^3+m^2+m+5  #
Wdimmax = max(Wrow, Wcol)
print "dim of W:", Wdimmax

Iw = matrix.identity(w)
Pw = Matrix(ZZ,[[ZZ(((i+1)%w)==j) for i in range(w)] for j in range(w)])  # some non-identity matrix P of dimension w
Pinvw = Matrix(ZZ,[[ZZ(((i-1)%w)==j) for i in range(w)] for j in range(w)])  # P^{-1}
print "I =", Iw
print "P =", Pw
print "Pinverse =", Pinvw
print "P*P^{-1} =", Pw*Pinvw


def rand_full_rank_MatR(k,l):
    """ generate a random full rank kxl matrix in R """
    M = Matrix(R,[[R.random_element() for i in range(l)] for j in range(k)])
    while M.rank()<k and M.rank()<l:
        M = Matrix(R,[[R.random_element() for i in range(l)] for j in range(k)])
    return M

def rand_rank_one_MatR(k,l):
    """ generate a random kxl matrix of rank 1 """
    M1 = Matrix(R,[[R.random_element() for i in range(1)] for j in range(k)])
    M2 = Matrix(R,[[R.random_element() for i in range(l)] for j in range(1)])
    return M1*M2

def pad_diagonal_rand(M):
    """ turn M into diag(RM1, RM2, M), where RM1, RM2 are random matrices of dimension r"""
    RM1 = rand_full_rank_MatR(r,r)
    RM2 = rand_full_rank_MatR(r,r)
    RR = block_matrix( [[RM1, matrix(R,r,r)],[matrix(R,r,r), RM2]]  )
    RRM = block_matrix( [[RR, matrix(R,2*r,w)],[matrix(R,w, 2*r), M]]  )
    return RRM

def JGen():
    """
    generate the leftbookend, make sure all the entries except the first r entries are non-zero
    we always use this trick to generate nonzero random values: (R.random_element())^2+1, same below
    """
    M = Matrix(R,[(R.random_element())^2+1 for i in range(Jcol)] )
    for i in range(r):
        M[0,i]=0
    return M

def alphaGen():
    return (R.random_element())^2+1

def KilianGen(d):
    """ genenate K and Kinv """
    Ki = rand_full_rank_MatR(d,d)
    Kinv = 1/Ki
    return Ki, Kinv

def mapKtoj1j2(k, j1, j2):
    return (1-k%2)*(j1)+(k%2)*(j2)   # j1 or j2, depending on the parity of k.

def SEDevaluate(S,E,D,j1,j2,kappa):
    """ evaluate like e.g. Wj1j2 = SSSE+SSED+SEDD+EDDD when rep=2 """
    Wj1j2 = 0
    for k in range(kappa):
        SEDtemp = 1
        for kS in range(k):
            SEDtemp = SEDtemp*S[ mapKtoj1j2(kS, j1, j2) ][ kS ]
        SEDtemp = SEDtemp*E[ mapKtoj1j2(k, j1, j2) ][ k ]
        for kD in range(k+1, kappa):
            SEDtemp = SEDtemp*D[ mapKtoj1j2(kD, j1, j2) ][ kD ]
        Wj1j2 = Wj1j2 + SEDtemp
    return Wj1j2

def test(rep, mode):
    """
    rep = time of repetition. We set the degree of multilinearity as kappa = 2*rep, to simulate "XZXZ..." repeat for #rep times
    mode 1: all identity matrices except that Sx1[0]=P, Sz1[0]=P, Sx1[0]=P^-1
    mode 0 and anything else: all identity matrices
    S, E, D[j][k] represents the components, j in [Wdimmax], k in [kappa]
    S[j][k], j-th index combination, k-th branch
    same for E[j][k], D[j][k]
    """

    kappa = 2*rep

    J = JGen()

    # Kilian randomization
    Ki = [ KilianGen(Jcol) for k in range(kappa) ]

    S = [ [ alphaGen()*J*pad_diagonal_rand(Iw)*Ki[0][0] ] + [ alphaGen()*Ki[k-1][1]*pad_diagonal_rand(Iw)*Ki[k][0] for k in range(1,kappa) ] for j in range(Wdimmax) ]
    # the last S[\star][kappa-1] will never be used so we don't worry its incorrectness
    E = [ [ rand_full_rank_MatR(Jrow,m) ] + [ rand_full_rank_MatR(w+2*r,m) for k in range(1,kappa-1) ] + [ rand_full_rank_MatR(w+2*r,1) ] for j in range(Wdimmax) ]
    D = [ [ rand_full_rank_MatR(m,m) for k in range(kappa-1) ] + [ rand_full_rank_MatR(m,1) ] for j in range(Wdimmax) ]
    # the last S[\star][kappa-1] will never be used so we don't worry its incorrectness

    if mode==1:
        S[0][0] = alphaGen()*J*pad_diagonal_rand(Pw)*Ki[0][0]
        #S[0][1] = alphaGen()*Ki[0][1]*pad_diagonal_rand(Pw)*Ki[1][0]
        S[0][2] = alphaGen()*Ki[1][1]*pad_diagonal_rand(Pinvw)*Ki[2][0]
        #S[0][3] = alphaGen()*Ki[2][1]*pad_diagonal_rand(Pinvw)*Ki[3][0]

    W = block_matrix( [ [ SEDevaluate(S,E,D,j1,j2,kappa)   for j2 in range(Wcol)] for j1 in range(Wrow) ]  )

    print "W.rank = ", W.rank()

test(2,0)
test(2,1)
