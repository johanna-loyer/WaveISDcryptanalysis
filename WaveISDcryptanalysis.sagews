# Author: Johanna Loyer
# Contact: johanna.loyer@inria.fr
# Date: July 2023
# Version: 1

# Wave parameters n,k,w,kU,kV
WAVE1 =  8576,  4288/8576,   7668/8576,  2966/8576,  1322/8576
WAVE3 = 12544, 6272/12544, 11226/12544, 4335/12544, 1937/12544
WAVE5 = 16512, 8256/16512, 14784/16512, 5704/16512, 2552/16512

# References:
#    - [CDE21]  https://arxiv.org/pdf/2104.12810.pdf
#    - [BCDL19] https://ia.cr/2019/304
#    - [Sen23]  https://ia.cr/2023/588
#    - [Deb23]  https://arxiv.org/pdf/2304.03541.pdf
#    - [Wave] https://wave-sign.org/wave_documentation.pdf


# Finds a local minimum of function f in [a,b]
def find_min(f,a,b,tol=1e-6):
    gr = float( (sqrt(5) + 1)/2)
    c = b - (b - a) / gr ; d = a + (b - a) / gr
    while abs(c - d) > tol:
        if f(c) < f(d): b = d
        else: a = c
        c = b - (b - a)/gr ; d = a + (b - a)/gr
    return (a+b)/2, f((a+b)/2) # param, time(param)

q = 3.
def log2(X): return numerical_approx( log(X)/log(2.) )

# Entropy (See [Deb23, Lemma 2.1.1])
def h(x, q=2):
    if (x == 0): return 0
    if (x == 1): return log2(q-1)
    return -x * log2(x) - (1 - x) * log2(1-x) + x * log2(q-1)

# Inverse entropy
def hinv(y, q=2):
    x0 = 1.0 / q
    while h(x0, q) > y: x0 /= 2
    x1 = (q - 1.0) / q
    while h(x1 / 2, q) > y: x1 /= 2
    def f(x): return h(x, q) - y
    return find_root(f, x0, x1)

# Combination nCw
def comb(n,w): return n*h(w/n)


#==============================================#
#           Classical Message Attack           #
#==============================================#

# Given (H, s=e0·H^T), forge a signature e such that e·H^T=s and wt(e)=w.
# There exists at least one solution e0.
# Parameters:
#    - k: matrix H of size (n-k) x n
#    - w: target weight of e
#    - l: length of s'', syndrome in the subISD
#    - p: target weight of e''
#    - a: order of Wagner's algorithm

### ISD + Wagner, with float a
def P(k,w,l): return comb(1-k-l, w-k-l) + (w-k-l) -(1-k-l)*log2(3) # Pr[wt(e') = w-p | e'']
def ForgeSignature_wagner0(w,k):
    def f(l):
        Pr = float(P(k,w,l))
        return Pr + (k+l)/(2^(-l*log2(3) / Pr) -1)
    l = find_root(f, 0, (w - k)/1.01)
    a = int(float(-l*log2(3) / P(k,w,l))) ; print("condition:", log2(3)*l/a < (k+l)/(2**a-1))
    p = k+l
    return max(log2(3)*l/a, log2(3)*(1-k-l) -( w-p + comb(1-k-l, w-p) ))

### ISD + Wagner
def ForgeSignature_wagner_lap(w,k, l,a,p):
    #return max(log2(3)*l/a, log2(3)*(1-k-l) -( w-p + comb(1-k-l, w-p) )) # non-smoothed
    if a<3: return max(log2(3)*l/a, log2(3)*(1-k-l) -( w-p + comb(1-k-l, w-p) )) # Proposition 4 (non smoothed)
    return max( (log2(3)*l - (k+l)/(2**a-1/2))/(a-1) , log2(3)*(1-k-l) - (w-p + comb(1-k-l, w-p)) ) # Theorem 6 (smoothed)

def ForgeSignature_wagner_la(w,k, l,a):
    p=k+l ; return p, ForgeSignature_wagner_lap(w,k, l,a,p) # p=k+l is optimal
    def partial(p): return ForgeSignature_wagner_lap(w,k, l,a,p)
    return find_min(partial, 0, k+l) # p, time
def ForgeSignature_wagner_l(w,k, l):
    a = 1
    while log2(3)*l/a < (k+l)/(2**a-1): a += 1 # cond. w/ smoothing: log2(3)*l/(a-1) < (k+l)/(2**(a-1)-1) (+1 integrated in formula of function ForgeSignature_wagner_lap)
    a -= 1
    return a, ForgeSignature_wagner_la(w,k, l,a)[1]

def ForgeSignature_wagner(w,k):
    def partial(l): return ForgeSignature_wagner_l(w,k, l)[1]
    return find_min(partial, 0, (w-k)) # l, time
def param_wagner(w,k):
    l = ForgeSignature_wagner(w,k)[0]
    a = ForgeSignature_wagner_l(w,k,l)[0]
    p = ForgeSignature_wagner_la(w,k, l,a)[0]
    return l,a,p


#==============================================#
#            Quantum Message Attack            #
#==============================================#

### Quantum ISD + quantum Wagner
def QForgeSignature_wagner_lap(w,k, l,a,p):
    #return max(log2(3)*l/a, (( log2(3)*(1-k-l) )- ( w-p + comb(1-k-l, w-p) ))/2 ) # non-smoothed
    if a<3: return max(log2(3)*l/a, (( log2(3)*(1-k-l) )- ( w-p + comb(1-k-l, w-p) ))/2 ) # non-smoothed
    return max( (log2(3)*l - (k+l)/(2**a-1/2))/(a-1) , (( log2(3)*(1-k-l) )- ( w-p + comb(1-k-l, w-p) ))/2 ) # smoothed

def QForgeSignature_wagner_la(w,k, l,a): p=k+l ; return p, QForgeSignature_wagner_lap(w,k, l,a,p)
def QForgeSignature_wagner_l(w,k, l):
    a = 1
    while log2(3)*l/a < (k+l)/(2**a-1): a += 1
    a -= 1
    return a, QForgeSignature_wagner_la(w,k, l,a)[1]
def QForgeSignature_wagner(w,k):
    def partial(l): return QForgeSignature_wagner_l(w,k, l)[1]
    return find_min(partial, 0, (1-k)/2) # l, time
def Qparam_wagner(w,k):
    l = QForgeSignature_wagner(w,k)[0]
    a = QForgeSignature_wagner_l(w,k,l)[0]
    p = QForgeSignature_wagner_la(w,k, l,a)[0]
    return l,a,p


#==============================================#
#             Classical Key Attack             #
#==============================================#

# Given H, find a word e=(u|u) in the code (i.e. e·H^T=0) and of weight wt(e)=t.
# The existence of such an e is not guaranteed but happens with higher probability than in a random code.
# Parameters:
#    - k: matrix H of size (n-k) x n
#    - rate_U: relative rate of subcode U, where kU *n = rateU * (n/2)
#    - t: target weight of e
#    - l: length of s'', syndrome in the subISD
#    - p: target weight of e''
#    - a: order of Wagner's algorithm (in Dumer, a=1)

### ISD + Dumer

# Find a word (u|u) of weight t by Dumer's algorithm
def FindUU_DUMER_tlp(k,rate_U, t,l,p):
    return max(comb(k+l,p)/2+p/2 , (log2(3)*(1/2-rate_U/2) + comb(1,t)/2 ) - (comb(k+l,p)/2 +(t-p)/2 + comb(1-k-l,t-p)) )

def FindUU_DUMER_tl(k,rate_U, t,l): # Optimization on p
    #def f(p): return FindUU_DUMER_tlp(k,rate_U, t,l,p)
    #return find_local_minimum(f, max(0,t-1+k+l), min(k+l,t), tol=1e-3)[1]
    p = (k+l) * hinv(2*l*log2(3) / (k+l), 3)
    return FindUU_DUMER_tlp(k,rate_U, t,l,p)

def FindUU_DUMER_t(k,rate_U, t): # Optimization on l
    def f(l): return FindUU_DUMER_tl(k,rate_U, t,l)
    return find_min(f, 0, (1-k)/2) # l,time

def FindUU_DUMER(k, rate_U, pr=0): # Optimization on t
    def g(t): return FindUU_DUMER_t(k,rate_U, t)[1]
    GV = hinv((1-rate_U) * log2(3), 3)
    return find_min(g, GV, 1-rate_U) # t, time

def KeyAttack(k, kUV):
    kU, kV = kUV
    rate_U, rate_V = kU*2, kV*2
    uu = FindUU_DUMER(k, rate_U)[1]     # (u,u) in the public code
    vv = FindUU_DUMER(1-k, 1-rate_V)[1] # (v,v) in the dual public code
    return min(uu, vv) # raccourci


#==============================================#
#             Quantum Key Attack             #
#==============================================#

# Given H, find a word e=(u|u) in the code (i.e. e·H^T=0) and of weight wt(e)=t.
# The existence of such an e is not guaranteed but happens with higher probability than in a random code.
# Parameters:
#    - k: matrix H of size (n-k) x n
#    - rate_U: relative rate of subcode U, where kU *n = rateU * (n/2)
#    - t: target weight of e
#    - l: length of s'', syndrome in the subISD
#    - p: target weight of e''
#    - a: order of Wagner's algorithm (in Dumer, a=1)

### Quantum ISD + quantum Dumer

# Find a word (u|u) of weight t by Dumer's algorithm
def QFindUU_DUMER_tlp(k,rate_U, t,l,p):
    kU = rate_U/2
    return max(log2(3)*l , (comb(1,t)/4+log2(3)*(1/4-kU/2))-(t/4-p/3 + comb(k+l,p)/6 + comb(1-k-l,t-p)/2)  ) # test
    return max( l*log2(3) , (log2(3)*(1/4-kU/2) + comb(1,t)/4) - (t/4-p/2 + comb(1-k-l,t-p)/2) )

def QFindUU_DUMER_tl(k,rate_U, t,l): # Optimization on p
    p = (k+l) * hinv(3*l*log2(3) / (k+l), 3) # Fix p st. comb(k+l,p)/3 + p/3 = l*log2(3)
    return p, QFindUU_DUMER_tlp(k,rate_U, t,l,p)

def QFindUU_DUMER_t(k,rate_U, t): # Optimization on l
    def f(l): return QFindUU_DUMER_tl(k,rate_U, t,l)[1]
    return find_min(f, 0, (1-k)/2) # l,time

def QFindUU_DUMER(k, rate_U, pr=0): # Optimization on t
    def g(t): return QFindUU_DUMER_t(k,rate_U, t)[1]
    GV = hinv((1-rate_U) * log2(3), 3)
    return find_min(g, GV, 1-rate_U) # t, time

def QKeyAttack(k, kUV):
    kU, kV = kUV
    rate_U, rate_V = kU*2, kV*2
    uu = QFindUU_DUMER(k, rate_U)[1]     # (u,u) in the public code
    vv = QFindUU_DUMER(1-k, 1-rate_V)[1] # (v,v) in the dual public code
    return min(uu, vv) # raccourci

# The times to find a Type-U word in the code (uu) and in its dual (vv) are balanced. 
def Qparam_dumeru(k,kUV):
    kU,kV = kUV ; rate_U = 2*kU
    t = QFindUU_DUMER(k, rate_U)[0]
    l = QFindUU_DUMER_t(k,rate_U, t)[0]
    p = QFindUU_DUMER_tl(k,rate_U, t,l)[0]
    return t,l,p
def Qparam_dumerv(k,kUV):
    kU,kV = kUV ; rate_V = 2*kV
    t = QFindUU_DUMER(1-k, 1-rate_V)[0]
    l = QFindUU_DUMER_t(1-k, 1-rate_V, t)[0]
    p = QFindUU_DUMER_tl(1-k, 1-rate_V, t,l)[0]
    return t,l,p


#==============================================#
#        Results: Security level of Wave       #
#==============================================#

if 1: # Classical key attack
    n,k,w,kU,kV = WAVE1 ; kUV=(kU, kV) ; print("\n(I)  Classic Key attack: ", int(KeyAttack(k,kUV)*n))
    n,k,w,kU,kV = WAVE3 ; kUV=(kU, kV) ; print("(III)Classic Key attack: ", int(KeyAttack(k,kUV)*n))
    n,k,w,kU,kV = WAVE5 ; kUV=(kU, kV) ; print("(V)  Classic Key attack: ", int(KeyAttack(k,kUV)*n))

if 1: # Classical message attack
    n,k,w,kU,kV = WAVE1 ; print("(I)  Classic Msg attack: ", int(ForgeSignature_wagner(w,k)[1]*n))
    n,k,w,kU,kV = WAVE3 ; print("(III)Classic Msg attack: ", int(ForgeSignature_wagner(w,k)[1]*n))
    n,k,w,kU,kV = WAVE5 ; print("(V)  Classic Msg attack: ", int(ForgeSignature_wagner(w,k)[1]*n))

if 1: # Quantum key attack
    n,k,w,kU,kV = WAVE1 ; kUV=(kU, kV) ; print("\n(I)  Quantum Key attack: ", int(QKeyAttack(k, kUV)*n))
    n,k,w,kU,kV = WAVE3 ; kUV=(kU, kV) ; print("(III)Quantum Key attack: ", int(QKeyAttack(k, kUV)*n))
    n,k,w,kU,kV = WAVE5 ; kUV=(kU, kV) ; print("(V)  Quantum Key attack: ", int(QKeyAttack(k, kUV)*n))

if 1: # Quantum message attack
    n,k,w,kU,kV = WAVE1 ; print("\n(I)  Quantum Msg attack: ", int(QForgeSignature_wagner(w,k)[1]*n))
    n,k,w,kU,kV = WAVE3 ; print("(III)Quantum Msg attack: ", int(QForgeSignature_wagner(w,k)[1]*n))
    n,k,w,kU,kV = WAVE5 ; print("(V)  Quantum Msg attack: ", int(QForgeSignature_wagner(w,k)[1]*n))


#(I)  Classic Key attack:  138
#(III)Classic Key attack:  206
#(V)  Classic Key attack:  274

#(I)  Classic Msg attack:  129
#(III)Classic Msg attack:  194
#(V)  Classic Msg attack:  258

#(I)  Quantum Key attack:  80
#(III)Quantum Key attack:  120
#(V)  Quantum Key attack:  160

#(I)  Quantum Msg attack:  78
#(III)Quantum Msg attack:  117
#(V)  Quantum Msg attack:  156
