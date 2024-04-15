from .tool import *

"""
To bootstrap, we need sgn repn of type B/C,D
as symbols. 
"""


def sgnBC(n):
    """
    Generate the symbol of sgn representation of type B/C
    """
    return (tuple(range(n+1)),tuple(range(1,n+1)))

def sgnD(n):
    """
    Generate the symbol of sgn representation of type D 
    TODO: check the correctness
    """
    return (tuple(range(n)),tuple(range(1,n+1)))

  

"""
Compute  the J-induction of a symbol 
       ( a_0, a_1, ... , a_k )
tau =  (   b_1, ... , b_k )

from a maximal parabolic of the form W_{A_r} x W_{r_0} 
which are the symbol  

       ( a_0, a_1, ... , a_i +1, ... a_k )
tau =  (   b_1, ... , b_i +1, ..., b_k )

We will not check tau is a valide symbol
"""
def JindPara(tau,r):
    tauL, tauR= equiv_symbol_expend(tau,r)
    hr = r//2
    if hr == 0:
        tauL1,tauL2 = list(tauL), []
        tauR1,tauR2 = list(tauR), []
    else: 
        tauL1,tauL2 = tauL[:-hr], tauL[-hr:]
        tauR1,tauR2 = tauR[:-hr], tauR[-hr:]
    assert(len(tauL2)==len(tauR2))
    #print(f"({tauL1},{tauR1})")
    #print(f"({tauL2},{tauR2})")
    if r % 2 ==0:
        yield (tauL1+[a+1 for a in tauL2],tauR1 + [a+1 for a in tauR2])
    else:
        yield (tauL1[:-1] +[tauL1[-1]+1] + [a+1 for a in tauL2],tauR1 + [a+1 for a in tauR2])
        if len(tauR1) >0 and tauL1[-1]==tauR1[-1]:
            yield (tauL1 + [a+1 for a in tauL2],tauR1[:-1] + [tauR1[-1]+1]+ [a+1 for a in tauR2])


def JindPara(tau,r):
    def last(l):
        return l[-1] if len(l)>0 else -1
    tauL, tauR= equiv_symbol_expend(tau,r)
    resL,resR = [], []
    for _ in range(r-1): 
        if last(tauR) > last(tauL):
            resR = [tauR.pop()+1]+resR
        else:  
            resL = [tauL.pop()+1]+resL
    if last(tauL) >= last(tauR):    
        yield (tauL[:-1]+[tauL[-1]+1]+resL,tauR+resR)
    if last(tauL) <= last(tauR):    
        yield (tauL+resL,tauR[:-1]+[tauR[-1]+1]+resR)


def Jind(ltau, lr):
    """
    ltau is a list of a left cell
    lr is a list [r_1, r_2, ... r_k]
    The return is Jind_{W_A_r_1 x W_A_r_2 x ... W_A_r_k} ltau
    """
    if len(lr)==0 or lr[0]==0:
        return ltau
    return Jind([tau2 for tau1 in ltau for tau2 in JindPara(tau1,lr[0])],lr[1:])



