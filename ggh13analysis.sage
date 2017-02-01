# -*- coding: utf-8 -*-

"""
Cryptanalysis of GGHRSW based on GGH13.  https://eprint.iacr.org/2016/998
Candidate Obfuscator by Garg, Gentry, Halevi, Raykova, Sahai, Waters: https://eprint.iacr.org/2013/451
The code is modified from:
https://martinralbrecht.wordpress.com/2015/04/13/sage-code-for-ggh-cryptanalysis-by-hu-and-jia/

Modify "ggh13_#pattern_gen" to change how the obfuscated code (matrices) are generated
Modify "attack_Step#_for_#pattern" to try the different steps of the attack

Highlights of the simplifications in the proof-of-concept experiments:
1. We pretend that the zero-test passes so everything appear in R instead of R_q. The dummy branch is not included.
2. Simplify intervals X and Z.
Simplifications in details will be explained in the code.

Sometimes there will be "Zero divisor error", usually due to the failure of inverting mod <g>. When Norm(g) is small it is more likely to happen.
"""

from sage.structure.element import parent
from sage.functions.log import log
from sage.functions.other import sqrt, floor
from sage.rings.all import ZZ, IntegerModRing, CyclotomicField, QQ
 from sage.rings.arith import next_prime
from sage.matrix.constructor import matrix
from sage.misc.misc_c import prod

""" global parameters """
r = 2         # the dimension of padded random entries will be 2r, r :=m in the paper Section 3
w = 3         # the dimension of permutation matrices, minimum 5 for Barrington but 2 is enough for demonstrating the attack
rho = 2*r+w
Wdim = rho    # dimension of W needed to be accumulated

print "The dimension of padded random entries 2*r:", 2*r
print "The dimension of Barrington matrices w:", w

Iw = matrix.identity(w)
Pw = Matrix(ZZ,[[ZZ(((i+1)%w)==j) for i in range(w)] for j in range(w)])  # some w-cycle P
Pinvw = Matrix(ZZ,[[ZZ(((i-1)%w)==j) for i in range(w)] for j in range(w)])  # P^{-1}
#print "I =", Iw
#print "P =", Pw
#print "Pinverse =", Pinvw
#print "P*P^{-1} =", Pw*Pinvw

class GGH13:
    """
    A sloppy implementation of GGHLite.
    By "sloppy" we mean that we do not care about distributions -- Martin
    """

    def __init__(self, n, kappa):
        """
        Initialise a new sloppy GGHLite instance.
        :param n: dimension (must be power of two)
        :param kappa: multilinearity level  (Yilei: not used in the simplified examples)
        """
        self.n = ZZ(n)
        if not n.is_power_of(2):
            raise ValueError
        self.kappa = ZZ(kappa)

        self.R = ZZ["z"]
        self.K = CyclotomicField(2*n, "z")
        self.OK = self.K.ring_of_integers()
        self.f = self.R.gen()**self.n + 1

        self.sigma = self.n
        self.sigma_p = round(self.n**(ZZ(5)/2) * self.sigma)
        print "sigma_p: ", self.sigma_p
        self.sigma_s = round(self.n**(ZZ(3)/2) * self.sigma_p**2)

        self.q = next_prime(round(3*self.n**(ZZ(3)/2) * self.sigma_s*self.sigma_p)**(3*self.kappa))
        self.Rq = self.R.change_ring(IntegerModRing(self.q))

        g = self.discrete_gaussian(self.sigma)
        # we enforce primality to ensure we can invert mod ⟨g⟩
        while not self.K(g).is_prime():
            g = self.discrete_gaussian(self.sigma)

        h = self.discrete_gaussian(sqrt(self.q))
        z = self.Rq.random_element(degree=n-1)

        # zero testing parameter
        self.pzt = h*z**kappa * self.Rq(g).inverse_mod(self.f)

        self.J = self.K.ideal([g])
        self.S = self.K.quotient_ring(self.J)
        print "J = ",self.J
        print "S = ",self.S

        # we give the basis of <g>, used to check Step I
        self.G = self.canonical_basis(g)
        self.I = self.K.ideal([self.R(row.list()) for row in self.G.rows()])
        print "q=", self.q, "\ng=", g, "\nNorm of g:", self.OK(g).norm()
        print "B(G)=", self.G, "\nI=", self.I

        print "---End of generating secret and public parameters---"

        X, Y1, Y2, Y3, Z, a20_a2l, a1030_a1131 = self.ggh13XYZ_gen(g, Wdim, 2, Wdim, 0)
        BX, BY1, BY2, BY3, BZ, Ba20_a2l, Ba1030_a1131 = self.ggh13XYZ_gen(g, Wdim, 2, Wdim, 1)
        self.attack_StepI_for_XYZ(X, Y1, Y2, Y3, Z)
        self.attack_StepII_for_XYZ(X, Y1, Y2, Y3, Z, a20_a2l)
        self.attack_StepIII_for_XYZ(X, Y1, Y2, Y3, Z, a20_a2l, a1030_a1131)
        self.attack_StepIII_for_XYZ(BX, BY1, BY2, BY3, BZ, Ba20_a2l, Ba1030_a1131)

    def ggh13XYZ_gen(self, g, nx , ny , nz, mode):
        """
        integers nx, ny, nz denote the number of input combinations needed in intervals X, Y and Z
        Mode=0: all identity matrices
        Mode=1 is designed for verifying Step III the annihiliation attack
            BP: where P is some w-cycle. Note that it still computes all-identity function.
            0|I, I, I,  I     I
            1|I, P, I,  P^-1  I
            -----------------------
             |X  j1 j2  j1    Z
        """
        print "-----------------------------  "
        if mode==1:
            print "ggh13XYZ_gen_mode_1: instance generation for input partition pattern X|Y1|Y2|Y3|Z"
            print "all the matrices except Y1[1] and Y3[1] are identities. Moed 1 is only used in Step III"
        else:
            print "ggh13XYZ_gen_mode_0: instance generation for input partition pattern X|Y1|Y2|Y3|Z"
            print "all the matrices are identities. In Step I and II we will always use mode 0"
        print "-----------------------------  "
        J,L = self.JLGen()
        Kx, Kxinv = self.KilianGen()
        Ky1, Ky1inv = self.KilianGen()
        Ky2, Ky2inv = self.KilianGen()
        Ky3, Ky3inv = self.KilianGen()
        alphaY1 = [self.alphaGen() for i in range(ny)]
        alphaY2 = [self.alphaGen() for i in range(ny)]
        alphaY3 = [self.alphaGen() for i in range(ny)]
        #print "alpha list at Y2:", alphaY2
        a20_a2l = ((alphaY2[0].mod(self.I))*(alphaY2[1].inverse_mod(self.I))).mod(self.I)
        print "Used to verify Step II: alphaY2[0]*alphaY2[1]^{-1} mod I:", a20_a2l
        a1030_a1131 = ( (alphaY1[0].mod(self.I))*(alphaY3[0].mod(self.I))*(alphaY1[1].inverse_mod(self.I))*(alphaY3[1].inverse_mod(self.I)) ).mod(self.I)
        print "Additionally used in step III, alphaY1[0]*alphaY3[0]*(alphaY1[1]*alphaY3[1])^{-1} mod I:", a1030_a1131

        X = [ (self.alphaGen() * J * self.pad_diagonal_rand(Iw) * Kx + self.K(g)*self.rand_full_rank_MatK(1,rho))/self.K(g) for i in range(nx)]
        Y1 = [ (alphaY1[i]*Kxinv*self.pad_diagonal_rand(Iw)*Ky1 + self.K(g)*self.rand_full_rank_MatK(rho,rho)) for i in range(ny)]
        Y2 = [ (alphaY2[i]*Ky1inv*self.pad_diagonal_rand(Iw)*Ky2 + self.K(g)*self.rand_full_rank_MatK(rho,rho)) for i in range(ny)]
        Y3 = [ (alphaY3[i]*Ky2inv*self.pad_diagonal_rand(Iw)*Ky3 + self.K(g)*self.rand_full_rank_MatK(rho,rho)) for i in range(ny)]
        Z = [ (self.alphaGen() *Ky3inv*self.pad_diagonal_rand(Iw)* L  + self.K(g)*self.rand_full_rank_MatK(rho,1) ) for i in range(nz)]

        if mode==1:
            Y1[1] = alphaY1[1]*Kxinv*self.pad_diagonal_rand(Pw)*Ky1 + self.K(g)*self.rand_full_rank_MatK(rho,rho)
            Y3[1] = alphaY1[1]*Ky2inv*self.pad_diagonal_rand(Pinvw)*Ky3 + self.K(g)*self.rand_full_rank_MatK(rho,rho)

        print "==== Obfuscated code generated for mode", mode
        return X, Y1, Y2, Y3, Z, a20_a2l, a1030_a1131

    def attack_StepI_for_XYZ(self, X, Y1,Y2,Y3, Z):
        """
            Attack Step I for branching programs with input partition pattern X|Y|Z
        """
        print "\nStep I: find elements in I = <g>:"
        W00 = block_matrix( [ [ X[i] * Y1[0]*Y2[0]*Y3[0]* Z[j]   for j in range(Wdim)] for i in range(Wdim) ]  )
        W01 = block_matrix( [ [ X[i] * Y1[0]*Y2[1]*Y3[0]* Z[j]   for j in range(Wdim)] for i in range(Wdim) ]  )
        W10 = block_matrix( [ [ X[i] * Y1[1]*Y2[0]*Y3[0]* Z[j]   for j in range(Wdim)] for i in range(Wdim) ]  )
        W11 = block_matrix( [ [ X[i] * Y1[1]*Y2[1]*Y3[0]* Z[j]   for j in range(Wdim)] for i in range(Wdim) ]  )
        M = block_matrix( [[W00, W10], [W01, W11]] )
        N = block_matrix( [[W00, W01], [W10, W10]] )

        #print M.rank()
        #print N.rank()
        Q = M/N
        Qdet = Q.determinant()
        print "the determinant of Q=M/N:", Qdet
        print "the numerator of Qdet:", self.extract_numberator(Qdet)
        print "Numerator of detQ mod I:", self.extract_numberator(Qdet).mod(self.I)
        print "--------- if detQ!=0 and detQ mod I = 0, then Step I passes. ------"

    def attack_StepII_for_XYZ(self, X, Y1,Y2,Y3, Z, a20_a2l):
        """
            Attack Step II for branching programs with input partition pattern X|Y|Z
        """
        print "\nStep II: recover the ratios of scalars alpha_{y2}^(0)/alpha_{y2}^(1):"
        W0 = block_matrix(self.K, [ [ X[i] * Y1[0]*Y2[0]*Y3[0]* Z[j]   for j in range(Wdim)] for i in range(Wdim) ]  )
        W1 = block_matrix(self.K, [ [ X[i] * Y1[0]*Y2[1]*Y3[0]* Z[j]   for j in range(Wdim)] for i in range(Wdim) ]  )
        #print W1
        Q = W0/W1
        print "W0/W1 = ", Q
        QmodI = self.matrixKmodI(Q, Wdim, Wdim)
        print "W0/W1 mod I = ", QmodI
        print "don't know how to code finding eigenvalues in R/I, can only verify "
        # if generate QmodI in S = R/I, then computing eigenvalue from there is not supported...
        XQ = QmodI.charpoly()
        print "The charpoly of W0/W1 mod I: chi", XQ
        print "chi(a0/a1):", XQ(a20_a2l).mod(self.I)
        print "--------- if chi(a0/a1)=0 then Step II passes. ------"

    def attack_StepIII_for_XYZ(self, X, Y1,Y2,Y3, Z, a20_a2l, a1030_a1131):
        print "\nStep III: compute the rank of A, distinguisher tells whether rank(A)>2r or not. \n A := W00 + a1030_a1131*a20_a2l*W11 - a20_a2l*W01 - a1030_a1131*W10 mod I "
        # here Y1 and Y3 are controlled by the same input bit
        W00 = block_matrix(self.K, [ [ X[i] * Y1[0]*Y2[0]*Y3[0]* Z[j]   for j in range(Wdim)] for i in range(Wdim) ]  )
        W10 = block_matrix(self.K, [ [ X[i] * Y1[1]*Y2[0]*Y3[1]* Z[j]   for j in range(Wdim)] for i in range(Wdim) ]  )
        W01 = block_matrix(self.K, [ [ X[i] * Y1[0]*Y2[1]*Y3[0]* Z[j]   for j in range(Wdim)] for i in range(Wdim) ]  )
        W11 = block_matrix(self.K, [ [ X[i] * Y1[1]*Y2[1]*Y3[1]* Z[j]   for j in range(Wdim)] for i in range(Wdim) ]  )
        A = a1030_a1131*a20_a2l*W11 + W00 - a1030_a1131*W10 - a20_a2l*W01
        annipolymat = self.matrixKmodI(A, Wdim, Wdim)
        print "The matrix A mod I:", annipolymat
        AinS = matrix(self.S, annipolymat)
        print "The rank of matrix A mod I:", AinS.rank()
        print "-------- If from mode 0, then the rank shall be 2*r whp; if from mode 1, then the rank shall be 2*r+1 whp -------"


    def matrixKmodI(self, M, row, col):
        """ Input a matrix M over K, output M mod I  """
        common_denominator = self.extract_denominator(M[0,0])
        for i in range(row):
            for j in range(col):
                common_denominator = lcm( self.extract_denominator(M[i,j]), common_denominator )
        MmodI = M*common_denominator
        cdmodI = self.K(common_denominator).inverse_mod(self.I)
        for i in range(row):
            for j in range(col):
                MmodI[i,j] =  (self.K(MmodI[i,j].mod(self.I))*cdmodI).mod(self.I)
        return MmodI

    def extract_numberator(self, intK):
        """Input an element in K, output its numerator, by multiplying the common denominator on everything"""
        return intK*self.extract_denominator(intK)

    def extract_denominator(self, intK):
        """Input an element in K, output its common denominator, only work when n>=2 """
        common_denominator = lcm( intK[0].denominator(), intK[1].denominator() )
        for i in range(2, self.n):
            common_denominator = lcm( intK[i].denominator(), common_denominator )
        return common_denominator

    def ggh13XZ_gen(self, g, nx , ny , nz):
        """
            instance generation for input partition pattern X|Y1|X2|Y2|Z, to simulate 2 partition (Take X|Y1|X2|Y2 as the same interval)
            integers nx, ny, nz denote the number of input combinations needed in intervals X, Y and Z
            This instance is only used to verify Step I. Step II and III requires 3 partitioning.
        """
        J,L = self.JLGen()
        print "J=", J
        print "L=", L
        Kx, Kxinv = self.KilianGen()
        Ky1, Ky1inv = self.KilianGen()
        Kx2, Kx2inv = self.KilianGen()
        Ky2, Ky2inv = self.KilianGen()

        X = [ (self.alphaGen() * J * self.pad_diagonal_rand(Iw) * Kx + self.K(g)*self.rand_full_rank_MatK(1,rho)) for i in range(nx)]
        Y1 = [ (self.alphaGen()*Kxinv*self.pad_diagonal_rand(Iw)*Ky1 + self.K(g)*self.rand_full_rank_MatK(rho,rho)) for i in range(ny)]
        X2 = [ (self.alphaGen()*Ky1inv*self.pad_diagonal_rand(Iw)* Kx2 + self.K(g)*self.rand_full_rank_MatK(rho,rho)) for i in range(nx)]
        Y2 = [ (self.alphaGen()*Kx2inv*self.pad_diagonal_rand(Iw)* Ky2 + self.K(g)*self.rand_full_rank_MatK(rho,rho)) for i in range(ny)]
        Z = [ (self.alphaGen() *Ky2inv*self.pad_diagonal_rand(Iw)* L  + self.K(g)*self.rand_full_rank_MatK(rho,1) ) for i in range(nz)]
        print "--- obfuscated code generated ---"
        return X, Y1, X2, Y2, Z

    def attack_StepI_for_XZ(self, X, Y1, X2, Y2, Z):
        """
            Attack Step I for branching programs with input partition pattern X|Y1|X2|Y2|Z
        """
        W00 = block_matrix( [ [ X[i] * Y1[0]*X2[i]*Y2[0]* Z[j]   for j in range(Wdim)] for i in range(Wdim) ]  )
        W01 = block_matrix( [ [ X[i] * Y1[0]*X2[i]*Y2[1]* Z[j]   for j in range(Wdim)] for i in range(Wdim) ]  )
        W10 = block_matrix( [ [ X[i] * Y1[1]*X2[i]*Y2[0]* Z[j]   for j in range(Wdim)] for i in range(Wdim) ]  )
        W11 = block_matrix( [ [ X[i] * Y1[1]*X2[i]*Y2[1]* Z[j]   for j in range(Wdim)] for i in range(Wdim) ]  )
        M = block_matrix( [[W00, W10], [W01, W11]] )
        N = block_matrix( [[W00, W01], [W10, W10]] )

        Q = M/N
        Qdet = Q.determinant()
        print "the determinant of Q=M/N:", Qdet
        print "the numerator of Qdet:", self.extract_numberator(Qdet)
        print "Numerator of detQ mod I:", self.extract_numberator(Qdet).mod(self.I)

    def rand_full_rank_MatK(self, k,l):
        """ generate a random full rank kxl matrix in K """
        M = Matrix(self.K,[[self.discrete_gaussian(self.sigma_p) for i in range(l)] for j in range(k)])
        while M.rank()<k and M.rank()<l:
            M = Matrix(self.K,[[self.discrete_gaussian(self.sigma_p) for i in range(l)] for j in range(k)])
        return M

    def pad_diagonal_rand(self, M):
        """
            Turn M into diag(RM1, RM2, M), where RM1, RM2 are random matrices of dimension r.
            This is the general setting from GMMSSZ https://eprint.iacr.org/2016/817,
            In GGHRSW, random entries are only padded on the diagonal
        """
        RM1 = self.rand_full_rank_MatK(r,r)
        RM2 = self.rand_full_rank_MatK(r,r)
        RR = block_matrix(self.K, [[RM1, matrix(self.K,r,r)],[matrix(self.K,r,r), RM2]]  )
        RRM = block_matrix(self.K, [[RR, matrix(self.K,2*r,w)],[matrix(self.K,w, 2*r), M]]  )
        return RRM

    def JLGen(self):
        """    generate bookends J and L    """
        J = Matrix(self.K,[ self.discrete_gaussian(self.sigma_p) for i in range(rho)] )
        L = Matrix(self.K,[ [ self.discrete_gaussian(self.sigma_p)] for i in range(rho)] )
        for i in range(r):
            J[0,i]=0
            L[r+i,0]=0
        return J, L

    def alphaGen(self):
        return self.K(self.discrete_gaussian(self.sigma_p))

    def KilianGen(self):
        """ genenate K and Kinv """
        Ki = self.rand_full_rank_MatK(rho,rho)
        Kinv = 1/Ki
        return Ki, Kinv

    def discrete_gaussian(self, sigma):
        """
        sample element with coefficients bounded by sigma
        .. note:: this is obviously not a discrete Gaussian, but we don't care here.
        """
        sigma = round(sigma)
        return self.R.random_element(x=-sigma, y=sigma, degree=self.n-1)

    @staticmethod
    def norm(f):
        "Return log of Euclidean norm of `f`"
        return log(max(map(abs, f)), 2.).n()

    def canonical_basis(self, g):
        "Return HNF of g"
        x = self.R.gen()
        n = self.n
        G = [x**n + ((x**i * g) % self.f) for i in range(n)]
        G = [r.list()[:-1] for r in G]
        G = matrix(ZZ, n, n, G)
        return G.hermite_form()

# inputs: n -> Z[X]/(X^n+1), must be power of two, n>=2; kappa: degree of multilinearity, but not used in this experiment
GGH13(4,3)
