from itertools import chain, combinations
from copy import copy, deepcopy


def concat_strblocks(*args, sep=' '):
    """
    Combine the arguments into a single block of strings
    """
    BLK = [ b.splitlines() for b in args]
    v = max((0, *(len(b) for b in BLK)))
    hBLK = [ max((0,*(len(r)  for r in b))) for b in BLK]
    res = []
    for i in range(v):
        l = [b[i]+' '*(hBLK[j]-len(b[i])) if i<len(b) else ' '*hBLK[j]
                  for j,b in enumerate(BLK)]
        res.append(sep.join(l))
    return '\n'.join(res)

def getz(C,idx,default=None):
    """
    Get the element in C[idx]
    if idx is out of the range, return the default value.
    """
    try:
        return C[idx]
    except IndexError:
        return default

def column2row(C):
    C=sorted(C)
    l= len(C)
    if l>0:
        c = C[0]
        return column2row([x-c for x in C[1:]])+[l for i in range(c)]
    else:
        return []

#diag_trans=column2row    

def reg_part(part, reverse=True):
    """
    Regularize the partition.
    It is a tuple of decresing sequence of positive integers
    """
    part = [x for x in part if x>0]
    part.sort(reverse=reverse)
    return tuple(part)

def reg_W_repn(tau, reverse=True):
    """
    Regularize the W_n repn paramterized by bipartition
    """
    ntau = (reg_part(tau[0], reverse=reverse),
            reg_part(tau[1], reverse=reverse))
    return ntau

def part_trans(part, reverse=True):
    part=sorted([x for x in part if x>0])
    if len(part) == 0:
        return []
    else:
        tpart = []
        for i in range(part[-1]):
            ri  = len([x for x in part if x>i])
            tpart.append(ri)
        return sorted(tpart, reverse=reverse)

    
def _simp_dec_seq(P):
    """
    return the simplify the sequence 
    [c_1, ..., c_k]
    strip zeros in the tail, 
    If the sequence is not decresing 
    return None # Note that [] != None
    """
    NP = []
    for i in range(len(P)):
        if P[i]< getz(P,i+1,0):
            return None
        elif P[i]>0:
            NP.append(P[i])
    return NP

simp_dec_seq = _simp_dec_seq



def simp_W_repn(tau):
    tauL, tauR = tau
    simpL = _simp_dec_seq(tauL)
    if simpL is None: 
        return None
    else:
        simpR = _simp_dec_seq(tauR)
        if simpR is None: 
            return None
        else:
            return (simpL,simpR)

def W_repn_sgn(tau):
    tauL, tauR = tau
    res = reg_W_repn((part_trans(tauR),
                       part_trans(tauL)))
    return res
    
def part_size(part):
    return sum(part)

   
def typeerr(part):
    raise ValueErrow('Wrong type %s'%rtype)
    
def switch_kv(D):
    RD = dict()
    for k,v in D.items():
        RD.setdefault(v, []).append(k)
    return RD

def BDcollapse(part):
    return partcollapse(part, 0)


def Ccollapse(part):
    if sum(part) %2 != 0:
        raise Exception('the partition has wrong pairty')
        return None
    return partcollapse(part, 1)

def partcollapse(part, pair = 0):
    """
    pair = 0 corresponding to type BD collapse
    pair = 1 corresponding to type C collapse
    """
    part = list(reg_part(part, reverse = True))
    #print(part)
    res = []
    l = len(part)
    i = 0
    while i < l:
        r = part[i] 
        j = 1
        while i+j < l and part[i+j] == r:
            j += 1
        if j % 2 == 0 or r % 2 != pair:
            res.extend(part[i:i+j])
            i = i+j
        else:
            res.extend(part[i:i+j-1])
            res.append(r-1) 
            i = i+j
            while i< l and part[i] == r-1:
                i += 1
                res.append(r-1)
            if i<l:
                part[i] = part[i]+1
            else:
                part.append(1)
                l = l+1
    return tuple(res) 

def partupplus(part):
    part = reg_part(part, reverse = True)
    if len(part) == 0:
        return (1,)
    else:
        return (part[0]+1, *part[1:])

def partupminus(part):
    part = reg_part(part, reverse = True)
    if len(part) == 0:
        return None
    else:
        if part[-1] == 1:
            return part[:-1]
        else:
            return (*part[:-1], part[-1]-1)
        
def tdualLS(part):
    """
    the part must be Type C
    part |--> (part^t)_D
    """
    assert(reg_part(part) == Ccollapse(part))
    return BDcollapse(part_trans(part))

def tdSP(part, col=False):
    """
    the part must be Type D
    part |-> ((part^+)^_)_C
    """
    if col:
        part = part_trans(part)
    assert(reg_part(part) == BDcollapse(part))
    respart = Ccollapse(partupminus(partupplus(part)))
    if col:
        respart = part_trans(respart)
    return respart 

def tdualBV(part):
    return tdSP(tdualLS(part))

def tdualBVW(part):
    tau = springer_part2repn(part, rtype = 'C')
    ttau = W_repn_sgn(tau)
    sttau = repn2specialrepn(ttau, rtype='D')
    sstau = (sttau[1], sttau[0])
    respart = springer_repn2part(sstau, rtype = 'C')
    return respart

def sign_twist_Wrepn(tau):
    return (part_trans(tau[1]), part_trans(tau[0]))

# data for define Barabasch-Vogan duality
# from the target rtype get
# (original rtype, special repn rtype, target rtype)
DTdualBVW= {
    'C': ('B','B','C'),
    'B': ('C','C','B'),
    'D': ('D','D','D'),
    'M': ('C','D','D'),
}

def dualBVW(part, rtype, partrc='r'):
    """
    The input:
    (part,rtype) = (a partition, the target root system type)
    the partition are represented by rows.
    the output:
    a partition, represented by rows by default.
    """
    # get the root system type of part
    (otype,stype,rtype) = DTdualBVW[rtype]
    tau = springer_part2repn(part,otype)
    stau = repn2specialrepn(tau, stype)
    sstau = sign_twist_Wrepn(stau)
    respart = springer_repn2part(sstau, rtype)
    if partrc == 'r':
        return respart
    elif partrc == 'c':
        return part_trans(respart)



def tdSPW(part, col=False):
    if col:
        part = part_trans(part)
    tau  = springer_part2repn(part, rtype = 'D')
    stau = repn2specialrepn(tau, rtype = 'D')
    sstau = (stau[1], stau[0])
    #print(sstau)
    respart = springer_repn2part(sstau, rtype = 'C')
    if col:
        respart = part_trans(respart)
    return respart

def tdualLSW(part):
    tau = springer_part2repn(part, rtype = 'C')
    ttau = W_repn_sgn(tau)
    sttau = repn2specialrepn(ttau, rtype='D')
    respart = springer_repn2part(sttau, rtype = 'D')
    return respart 
    
def repn2specialrepn(tau, rtype = 'C'):
    sym = repn2symbol(tau, rtype = rtype)
    ssym = symbol2specialsymbol(sym)
    restau = symbol2repn(ssym, rtype = rtype)
    return restau
    
    
def springer_part2repn(part, rtype='C', partrc='r' ):
    ## partition are
    if partrc == 'c':
        part = part_trans(part)
    part = sorted(part)
    if (rtype == 'C' and len(part)%2 == 1) or \
       (rtype == 'B' and len(part)%2 == 0) or \
       (rtype == 'D' and len(part)%2 == 1):
           part.insert(0, 0)
    pp = [lam+i for i, lam in enumerate(part)]
    pe, po = [],[]
    for lam in pp:
        if lam % 2 == 1:
            po.append(lam//2)
        else:
            pe.append(lam//2)
    tauL = tuple(xis - i for i, xis in enumerate(po))
    tauR = tuple(eta - i for i, eta in enumerate(pe))
    return (tauL,tauR)


def springer_part2family(part, rtype='C', partrc='r',report = False, reverse=True):
    ## partition are
    if partrc == 'c':
        part = part_trans(part)
    part = sorted(part)
    if (rtype == 'C' and len(part)%2 == 1) or \
       (rtype == 'B' and len(part)%2 == 0) or \
       (rtype == 'D' and len(part)%2 == 1):
           part.insert(0, 0)
    pp = [lam+i for i, lam in enumerate(part)]
    pe, po = [],[]
    for lam in pp:
        if lam % 2 == 1:
            po.append(lam//2)
        else:
            pe.append(lam//2)
    stau = symbol2repn((po,pe))

    ssym = repn2symbol(stau,rtype)
    Asyms = symbol2family(ssym)
    res = [symbol2repn(sym,reverse=reverse) for sym in Asyms]

    if report:
        print('Type %s orbit:'%rtype, part)
        print('Special repn:',stau)
        print('Totally %d repns:\n'%len(res),'\n '.join(map(str,res)))

    return res

def springer_dpart2family(part, rtype='C', symbol= False, reverse=True):
    """
    Compute the family from dual partition
    results is a list of W-repns represented by columns lengths.
    """
    part = sorted(part)
    if (rtype == 'C' and len(part)%2 == 1) or \
       (rtype == 'D' and len(part)%2 == 0) or \
       (rtype == 'B' and len(part)%2 == 1):
           part.insert(0, 0)
    pp = [lam+i for i, lam in enumerate(part)]
    pe, po = [],[]
    for lam in pp:
        if lam % 2 == 1:
            po.append(lam//2)
        else:
            pe.append(lam//2)
    stau = symbol2repn((po,pe))
    ssym = repn2symbol(stau, rtype)
    Asyms = symbol2family((ssym[1],ssym[0]))

    if report:
        print ('Special repn. %s'%str(stau))

    if symbol:
        return Asyms
    else:
        res = [symbol2repn(sym,reverse=reverse) for sym in Asyms]
        return res

def symbol2family(sym):
    symU, symD  = set(sym[0]), set(sym[1])
    k = len(symU - symD)
    mm = symU ^ symD
    cc = symU & symD
    res = []
    for uu in combinations(mm,k):
        uu = set(uu)
        U = tuple(sorted( uu | cc))
        D = tuple(sorted((mm-uu)|cc))
        res.append((U,D))
    return res

def symbol2specialsymbol(sym):
    return ssymbol2symbol(chain(*sym))


def ssymbol2symbol(ssym):
    """
    From the set of element to special symbol
    """
    ssym = sorted(ssym)
    tauL,tauR = [],[]
    for i in range(len(ssym)):
        if i%2 ==0 :
            tauL.append(ssym[i])
        else:
            tauR.append(ssym[i])
    return (tauL,tauR)



def springer_repn2part(tau, rtype = 'C'):
    tauL, tauR = tau
    if rtype == 'C':
        lL = max(len(tauL),len(tauR)+1)
        lR = lL-1 
        tauL = sorted([0]*(lL-len(tauL))+list(tauL))
        tauR = sorted([0]*(lR-len(tauR))+list(tauR))
        xis = [xi+2*i for i, xi in enumerate(tauL)]
        etas = [eta+2*i+1 for i, eta in enumerate(tauR)]
        ssym = sorted(xis+etas)
        ssymL, ssymR = ssymbol2symbol(ssym)
        """
        symbol = (xi_i + 2i; eta_i + 2i+1)
        """
        sxi = [lam-2*i for i, lam in enumerate(ssymL)]
        seta = [0] + [lam-2*i-1 for i,lam in enumerate(ssymR)]
        """
        Compute the partition
        """
        olams = [(lam+i)*2+1 for i, lam in enumerate(sxi)]
        elams = [(lam+i)*2 for i, lam in enumerate(seta)]
        part = [lam - i for i, lam in enumerate(sorted(olams+elams))]
        return reg_part(part)
    elif rtype == 'B' or rtype == 'D':
        if rtype == 'B':
            lL = max(len(tauL),len(tauR)+1)
            lR = lL-1 
        else:
            lR = lL = max(len(tauL),len(tauR))
        tauL = sorted([0]*(lL-len(tauL))+list(tauL))
        tauR = sorted([0]*(lR-len(tauR))+list(tauR))
        xis = [xi+2*i for i, xi in enumerate(tauL)]
        etas = [eta+2*i for i, eta in enumerate(tauR)]
        ssym = sorted(xis+etas)
        ssymL, ssymR = ssymbol2symbol(ssym)
        """
        symbol = (xi_i + 2i; eta_i + 2i+1)
        """
        sxi = [lam-2*i for i, lam in enumerate(ssymL)]
        seta = [lam-2*i for i,lam in enumerate(ssymR)]
        """
        Compute the partition
        """
        olams = [(lam+i)*2+1 for i, lam in enumerate(sxi)]
        elams = [(lam+i)*2 for i, lam in enumerate(seta)]
        part = [lam - i for i, lam in enumerate(sorted(olams+elams))]
        return reg_part(part)

def equiv_symbol(sym,l):
    symU, symL = sym
    l = max(l,0)
    symU = tuple(a+l for a in chain(range(-l,0),sorted(symU)))
    symL = tuple(a+l for a in chain(range(-l,0),sorted(symL)))
    return (symU, symL)


def _J_symbol(sym, n, rtype='C'):
    """
    U/L for upper and lower rows. 
    """
    l = (n-len(sym[0])-len(sym[1])+1)//2
    symU, symL = equiv_symbol(sym, l)
    symU, symL = list(symU),list(symL)
    i,j = len(symU)-1, len(symL)-1
    for a in range(n-1):
        if i>= 0 and j>=0:
            if symU[i]>=symL[j]:
                symU[i] = symU[i]+1
                i = i-1
            else:
                symL[j] = symL[j]+1
                j = j-1
        elif i<0:
                symL[j] = symL[j]+1
                j = j-1
        elif j<0:
                symU[i] = symU[i]+1
                i = i-1
    res = multiset()
    if i>= 0 and j>=0 and symU[i]==symL[j]:
        symU[i] = symU[i]+1
        res[(tuple(symU),tuple(symL))] = 1
        symU[i] = symU[i]-1
        symL[j] = symL[j]+1
        res[(tuple(symU),tuple(symL))] = 1
    elif (i>=0 and j<0) or symU[i]>symL[j]:
        symU[i] = symU[i]+1
        res[(tuple(symU),tuple(symL))] = 1
    elif (j>=0 and i<0): 
        symL[j] = symL[j]+0
        res[(tuple(symU),tuple(symL))] = 1
    return res 
                




def symbol2repn(sym, rtype = 'C', reverse=False):
    symL, symR = sym
    tauL = tuple(lam-i for i, lam in enumerate(symL))
    tauR = tuple(lam-i for i, lam in enumerate(symR))
    return reg_W_repn((tauL, tauR), reverse=reverse)

def repn2symbol(tau, rtype='C'):
    tauL,tauR = reg_W_repn(tau, reverse=False)
    if rtype == 'C' or rtype == 'B':
        lL = max(len(tauL),len(tauR)+1)
        lR = lL-1
    elif rtype == 'D':
        lR = lL = max(len(tauL),len(tauR))
    else:
        raise Exception('Wrong type',rtype)
    symL = tuple(i+lam for i, lam
                 in enumerate(chain((0,)*(lL-len(tauL)),tauL)))
    symR = tuple(i+lam for i, lam
                 in enumerate(chain((0,)*(lR-len(tauR)),tauR)))
    return (symL,symR)

def isspecial_BC(symb):
    symL, symR = symb
    assert(len(symL) == len(symR)+1)
    for i, mu in enumerate(symR):
        if symL[i]>mu or symL[i+1]<mu:
           return False
    return True

def isspecial_symbol(symb, rtype='C'):
    symL, symR = symb
    if rtype == 'C' or rtype == 'B':
        return isspecial_BC(symb)
    elif rtype == 'D':
        res = (isspecial_BC(((0, *symL), symR)) or
               isspecial_BC(((0, * symR), symL)))             
        return res



def part2srepn(part, rtype='C'):
    tau = springer_part2repn(part,rtype)
    RES = Wrepn2srepn(tau,rtype)
    return RES

def Wrepn2srepn(tau, rtype='C'):
    symb1 = repn2symbol(tau,rtype)
    symb = symbol2specialsymbol(symb1)
    res = symbol2repn(symb,rtype)
    return res

def part2dbcell(part, rtype='C'):
    tau = springer_part2repn(part,rtype)
    RES = Wrepn2dbcell(tau,rtype)
    return RES

def Wrepn2dbcell(tau, rtype='C'):
    symb1 = repn2symbol(tau,rtype)
    #print(symb1)
    (up,down)= symbol2specialsymbol(symb1)
    DIFF = set(up) ^ set(down)
    #print(DIFF)
    cc = set(up) - DIFF
    uup = set(up) - cc
    ddown = set(down) - cc
    RES = []
    for k in range(len(ddown)+1):
        for td in combinations(ddown,k):
            for tu in combinations(uup,k):
                uu = sorted(uup-set(tu)|set(td)|cc)
                dd = sorted(ddown-set(td)|set(tu)|cc)
                RES.append(symbol2repn((uu,dd)))
    return RES
