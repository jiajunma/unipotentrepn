from collections import Counter

from .tool import *
from .jind import *

def rstr_mpartition(nu,lam):
    return '['+', '.join(f"[bold red]{r}[/bold red]"if r in nu else f"{r}" for r in lam)+']'

def multiset_diff(a,b):
    """
    Suppose a is a multiset and b is a set, this function returns
    a - b where b is viewed as a multiset with no duplication.
    """
    return Multiset(a) - Multiset(b)

def allDistRmarkingBD(n):
    """
    The following function generates all distinguished reduced marking 
    """
    for lam in BDpartitions(n):
        nu0  = sorted(set(multiset_diff(lam,set(lam))),reverse=True)
        nuall = MarkableBD(lam) 
        for nu1  in sublists(list(set(nuall)-set(nu0))):
            nu = nu0+nu1
            if isBDDistingushed(nu,lam):
                yield (nu,lam)

def twogammaDistBD(nu :list[int],lam:list[int]):
    assert(isBDDistingushed(nu,lam))
    nu = sorted(nu,reverse=True)
    p= sorted (lam,reverse=True)
    internu = []
    for i in range(len(nu)//2):
        internu.extend(a for a in p if a < nu[2*i] and a > nu[2*i+1])
        internu.append(nu[2*i])
        if p.count(nu[2*i+1]) > 1:
            internu.append(nu[2*i+1])
    other = sorted(Multiset(p)-Multiset(internu),reverse=True)
    #print(f"internu = {internu}, other = {other}")
    internu = sorted(internu,reverse=True)
    part  = list_up(internu) + other 
    return twogamma_part(sum(lam)//2,part)
    
"""
Fix an integral infinitesimal character gamma,
Let W_gamma be the stablizer of gamma in W.
Let W(gamma) be the integral Weyl group of gamma.
the Lusztig cell is given by 
J-ind_{W_gamma}^{W(gamma)} (sgn) \otimes sgn
"""


"""
Let G = type BCD
If gamma = (g_1 = g_2 = ... = g_k_1 > g_{k_1+1}  = g_{k_1+2} = g_{k_1+k_2} > g_{k_1+k_2+1} = ... = g_{k_1+k_2+k_3} > 0 = 0 = ... = 0) 
Assume there are k_0 zeros in gamma
then W_gamma = W_{A_k_1} x W_{A_k_2} x W_{A_k_3} x ... x W_{k_r} x W_{k_0,BCD}

Wgamma send gamma to the tuples 
((k_0, [k'_1,k'_2,...,k'_r']), # of even parts 
   (0, [k''_1,k''_2,...,k''_r''])) # of odd parts
"""
def Wgamma(gamma):
    c = Counter(gamma)
    return ((getz(c,0,0), [c[i] for i in c if i%2 == 0 and i > 0]),(0, [c[i] for i in c if i%2 == 1 and i > 0]))


def gamma2LusztigCellB(gamma):
    """
    This function returns the list of elements in the Lusztig cell of gamma
    """
    # Levi of even and odd parts
    Leven, Lodd = Wgamma(gamma)
    Ecell = Jind([sgnBC(Leven[0])],Leven[1])
    #Here we use the metaplectic cell
    Ocell = Jind([([0],[0])],Lodd[1])
    return(Ecell,Ocell)

def printCells(cell,bipart=False,reverse=True):
    for sym in cell:
        tau = symbol2repn(sym,reverse=reverse)
        if bipart:
            print(f"{tau}")
        else:
            print(f"{sym}")

def DLA2LusztigCellB(nu,lam):
    assert(isBDDistingushed(nu,lam))
    gamma = twogammaDistBD(nu,lam)
    Ecell, Ocell = gamma2LusztigCellB(gamma)
    return (Ecell,Ocell)

