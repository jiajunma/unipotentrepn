from rich import print
from rich.table import Table
import itertools
from copy import copy, deepcopy

from multiset import FrozenMultiset as frozenset
from multiset import Multiset as multiset

from .tool import *

"""
In this program rtype is the \star in our paper.
rtype = B, C, D, M=\widetilde{C}



In this new version, we dose not use the counting program for type C 
to deduce the counting for type B

If tau = (tauL,tauR) is the representation for type B, then tau' = (tauR^t, tauL^t) 
is the corresponding representation for type C
 Type B  <---> Type C
      r  <--->  c
      r' <--->  c'
      c  <--->  r
"""

def allsubsets(S):
    k  = len(S)
    for i in range(k+1):
        for SS in itertools.combinations(S,i):
            yield SS


def is_part_valid(part,rtype):
    """
    rtype in {B,C,D}
    """
    part = reg_part(part)
    # The total parity must be correct!
    p = sum(part)%2
    if (p == 0 and rtype == 'B') or (p == 1 and rtype in 'CD'):
        return False

    if rtype in 'BD':
        return part == BDcollapse(part)
    elif rtype in 'C':
        return part == Ccollapse(part)
    else:
        return False

def split_part(part,rtype):
    """
    rtype  = star, which is the type of root system
    Split partitions into good and bad parts.
    (part, rtype) --> (gpart, bpart)
    gpart: Good part
    bpart: Bad part
    """
    part = reg_part(part)
    if (not is_part_valid(part,rtype)) or (not rtype in 'BCD') :
        raise TypeError
    if rtype in 'BD':
        gpart = (*(r for r in part if r%2 == 1),)
        bpart = (*(r for r in part if r%2 == 0),)
    elif rtype == 'C':
        gpart = (*(r for r in part if r%2 == 0),)
        bpart = (*(r for r in part if r%2 == 1),)
    return (gpart, bpart)

def bpart2Wrepn(part,rtype):
    """
    Bad parity partition to the Weyl group representation.
    the function will not check the partition is good or not.
    rtype in {B,C,D,M}
    """
    part = reg_part(part)
    assert(len(part)%2 == 0)
    if rtype in 'CD':
        tauL = tuple(part[i]//2 for i in range(0,len(part), 2))
        tauR = tuple(part[i]//2 for i in range(0,len(part), 2))
        return (tauL,tauR)
    elif rtype in 'BM':
        tauL = tuple((part[i]+1)//2 for i in range(0,len(part), 2))
        tauR = tuple((part[i]-1)//2 for i in range(0,len(part),2))
        return (tauL,tauR)



def dualpart2Wrepn(part, rtype):
    """
    Assume the orbit has good parity. (the function will not check the condition)
    """
    part = sorted([x for x in part if x>0],reverse=True)
    a, res = divmod(len(part),2)
    if rtype == 'M' and res == 1:
        part = part + [0]
        a = a+1
    elif rtype == 'C' and res ==1:
        part = part + [-1]
        a = a+1
    elif rtype == 'B' and res ==0:
        part = part + [0]
    elif rtype == 'D' and res ==0:
        # a trick
        part = part + [-1]
    RES = []
    if rtype in 'BD':
        PPidx = [ i for i in range(a)
                  if part[2*i+1]>part[2*i+2] and part[2*i+2]>=0]
    elif rtype in 'CM':
        PPidx = [i for i in range(a)
                  if part[2*i]>part[2*i+1] and part[2*i+1]>=0]
    if rtype in 'BM':
        if rtype == 'B':
            otauL, otauR = [],[part[0]//2]
            part = part[1:]
        else:
            otauL, otauR = [],[]
        for P in allsubsets(PPidx):
            tauL,tauR = [],[]
            for i in range(a):
                if i in P:
                    tauL.append(part[2*i+1]//2)
                    tauR.append(part[2*i+0]//2)
                else:
                    tauL.append(part[2*i+0]//2)
                    tauR.append(part[2*i+1]//2)
            RES.append(reg_W_repn((tuple(otauL+tauL),tuple(otauR+tauR))))
    elif rtype in 'DC':
        if rtype == 'D':
            otauL, otauR = [(part[0]+1)//2],[]
            part = part[1:]
        else:
            otauL, otauR = [],[]
        for P in allsubsets(PPidx):
            tauL,tauR = [],[]
            for i in range(a):
                if i in P:
                    tauR.append((part[2*i+1]-1)//2)
                    tauL.append((part[2*i+0]+1)//2)
                else:
                    tauR.append((part[2*i+0]-1)//2)
                    tauL.append((part[2*i+1]+1)//2)
            RES.append(reg_W_repn((tuple(otauL+tauL),tuple(otauR+tauR))))
    return RES


def dualpart2LC(part, rtype):
    """
    Send a dual orbit with good parity to the corresponding Lusztig left cell.
    Assume the orbit has good parity. (the function will not check the condition)
    return: a dictionary \wp -> \tau_\wp
    """
    part = sorted([x for x in part if x>0],reverse=True)
    a, res = divmod(len(part),2)
    if rtype == 'M' and res == 1:
        part = part + [0]
        a = a+1
    elif rtype == 'C' and res ==1:
        part = part + [-1]
        a = a+1
    elif rtype == 'B' and res ==0:
        part = part + [0]
    elif rtype == 'D' and res ==0:
        # a trick
        part = part + [-1]
    RES = dict()
    if rtype in 'BD':
        PPidx = [ i for i in range(a)
                  if part[2*i+1]>part[2*i+2] and part[2*i+2]>=0]
    elif rtype in 'CM':
        PPidx = [i for i in range(a)
                  if part[2*i]>part[2*i+1] and part[2*i+1]>=0]
    if rtype in 'BM':
        if rtype == 'B':
            otauL, otauR = [],[part[0]//2]
            part = part[1:]
        else:
            otauL, otauR = [],[]
        for P in allsubsets(PPidx):
            tauL,tauR = [],[]
            for i in range(a):
                if i in P:
                    tauL.append(part[2*i+1]//2)
                    tauR.append(part[2*i+0]//2)
                else:
                    tauL.append(part[2*i+0]//2)
                    tauR.append(part[2*i+1]//2)
            tauP = reg_W_repn((tuple(otauL+tauL),tuple(otauR+tauR)))
            RES[frozenset(P)]=  tauP
    elif rtype in 'DC':
        if rtype == 'D':
            otauL, otauR = [(part[0]+1)//2],[]
            part = part[1:]
        else:
            otauL, otauR = [],[]
        for P in allsubsets(PPidx):
            tauL,tauR = [],[]
            for i in range(a):
                if i in P:
                    tauR.append((part[2*i+1]-1)//2)
                    tauL.append((part[2*i+0]+1)//2)
                else:
                    tauR.append((part[2*i+0]-1)//2)
                    tauL.append((part[2*i+1]+1)//2)
            tauP = reg_W_repn((tuple(otauL+tauL),tuple(otauR+tauR)))
            RES[frozenset(P)]=  tauP
    return RES

def LC2pbps(LC,rtype):
    """
    Input: dictionary of left repn, root type
    Output: dictionary of list of pbp in each shape
    """
    RES = dict()
    for PP, tau in LC.items():
        pbps = [pbp for pbp in Wrepn2pbps(tau,rtype)]
        RES[PP] = pbps
    return RES

# Translate a columne for type M.
transM = str.maketrans('*rscd','*srdc')

def _tpbpM(C):
    return C.translate(transM)


def testpbptwist(dO,rtype, print=print, report=False):
    print(r'Let $\mathcal O^\vee$ has rows $%s$'%(list(dO),))
    O = dualBVW(dO,rtype,partrc='c')
    print(r'Then $\mathcal O$ has columns $%s$'%(O,))
    WLC = dualpart2LC(dO,rtype)

    for pp, tau in WLC.items():
        if len(pp)==0:
            print(f"The special representation (columns) $\\{{\\}}\\mapsto \\tau_s =$ {tau[0]} $\\times$ {tau[1]}.")
        else:
            print(f"a non-special representation {set(pp)}$\\mapsto \\tau =$ {tau[0]} $\\times$ {tau[1]}.")

    PBPlist = LC2pbps(WLC,rtype)

    ### Test twist-up
    for pp in PBPlist:
        if len(pp)==0:
            continue
        p = min(pp, default=-1)
        print(f"The minimal p is {min(pp,default=-1)}")
        assert(p!=-1)
        ppd = frozenset(pp - set([p]))
        pbplistd= PBPlist[ppd]
        pbplistu = frozenset(twistpbpup(pbp,p,rtype,report=report) for pbp in pbplistd)
        print(f"The pbp-down list has $\\wp=$  {set(ppd)} size {len(set(pbplistd))}")
        print(f"The pbp-up list has $\\wp'=$  {set(pp)} size {len(set(pbplistu))}")
        #print(PBPlist[PPd])
        #print(pbpdowns)
        print(frozenset(PBPlist[pp])-frozenset(pbplistu))
        print(frozenset(pbplistu)-frozenset(PBPlist[pp]))
        #printpbplist(pbpdowns)
        print(frozenset(PBPlist[pp])==frozenset(pbplistu))


def twistpbpup(pbp,p,rtype, report=False):
    pbp = reg_drc(pbp)
    pbpL,pbpR = pbp
    cols  = max(len(pbpL),len(pbpR))
    if rtype == 'M':
        pbppL = tuple(getz(pbpL,i,'') if i != p else _tpbpM(getz(pbpR,p,'')) for i in range(cols))
        pbppR = tuple(getz(pbpR,i,'') if i != p else _tpbpM(getz(pbpL,p,'')) for i in range(cols))
        res = (pbppL,pbppR)
    elif rtype == 'C':
        # The original columns
        pbppL = list(getz(pbpL,i,'') if i != p else '' for i in range(cols))
        pbppR = list(getz(pbpR,i,'') if i != p else '' for i in range(cols))
        Lo, Ro = getz(pbpL,p,''), getz(pbpR,p,'')
        assert(len(Ro)>0)
        s = len(Ro)-len(Lo)
        x2 = getz(getz(pbpL,p+1,''),len(Lo)-1,'')
        x1 = Lo[-1]
        Rn = Ro[:-s-1]
        if x1 == '*':
            if x2=='r':
                Ln = Lo[:-1]+'r'*s+'rd'
                pbppL[p+1] = pbppL[p+1][:-1]+'c'
            else:
                Ln = Lo[:-1]+'r'*s+'cd'
        else:
            x0= getz(Lo,-2,'')
            if x0 == 'c':
                Ln = Lo[:-2]+'r'*(s+1)+'cd'
            else:
                Ln = Lo[:-1]+'r'*(s+1)+Lo[-1]
        if p != 0:
            LLn = pbppL[p-1]
            LRn = pbppR[p-1]
            if len(LRn) == len(Ln)-1:
                rs = 1
            else:
                rs = 2
            y0, y2  = Ln[-2], Ln[-1]
            y1 = LLn[len(Ln)-1]
            if (y1,y2) == ('r','r'):
                LLn = LLn[:len(Ln)-2]+'rr'+LLn[len(Ln):]
                LRn = LRn[:len(Ln)-2]+'s'*rs+LRn[len(Ln):]
                Ln = Ln[:len(Ln)-2]+'cd'
            elif (y1,y2) == ('c','r'):
                LLn = LLn[:len(Ln)-2]+'rc'+LLn[len(Ln):]
                LRn = LRn[:len(Ln)-2]+'s'*rs+LRn[len(Ln):]
                Ln = Ln[:len(Ln)-2]+'cd'
            elif (y1,y2) == ('d','r'):
                LLn = LLn[:len(Ln)-2]+'rd'+LLn[len(Ln):]
                LRn = LRn[:len(Ln)-2]+'s'*rs+LRn[len(Ln):]
                Ln = Ln[:len(Ln)-2]+'cd'
            elif (y1,y2) == ('d','c'):
                LLn = LLn[:len(Ln)-2]+'cd'+LLn[len(Ln):]
                LRn = LRn[:len(Ln)-2]+'s'*rs+LRn[len(Ln):]
                Ln = Ln[:len(Ln)-2]+'cd'
            pbppL[p-1]=LLn
            pbppR[p-1]=LRn
        pbppL[p]=Ln
        pbppR[p]=Rn
        res = (pbppL, pbppR)
        # print(concat_strblocks(f'p={p}', str_dgms(pbp),"<===>",str_dgms(res)))
    if report:
        report_str = concat_strblocks(str_dgms(pbp),"<==>",str_dgms(res))
        print(report_str)
    res = reg_drc(res)
    if not verify_drc(res,rtype=rtype):
        print(Ro,Rn,s)
        print(concat_strblocks(f'p={p}', str_dgms(pbp),"<===>",str_dgms(res)))
        raise ValueError('Result in wrong PBP')
    return res

def printpbplist(pbplist):
    for pbp in pbplist:
        print(str_dgms(pbp))

def twistpbpdown(pbp,p,rtype):
    pbp = reg_drc(pbp)
    pbpL,pbpR = pbp
    cols  = max(len(pbpL),len(pbpR))
    if rtype == 'M':
        pbppL = tuple(getz(pbpL,i,'') if i != p else _tpbpM(getz(pbpR,p,'')) for i in range(cols))
        pbppR = tuple(getz(pbpR,i,'') if i != p else _tpbpM(getz(pbpL,p,'')) for i in range(cols))
        res = reg_drc((pbppL,pbppR))
    elif rtype == 'C':
        # Too complicate
        # Unfinished!!!
        pbppL = list(getz(pbpL,i,'') if i != p else '' for i in range(cols))
        pbppR = list(getz(pbpR,i,'') if i != p else '' for i in range(cols))
        Lo, Ro = getz(pbpL,p,''), getz(pbpR,p,'')
        s = len(Lo)-len(Ro)-2
        assert(s>=0)
        y1 = getz(getz(pbpL,p,''),len(Lo)-1,'')
        y1 = getz(getz(pbpL,p,''),len(Lo)-1,'')
        x2 = Ro[-s-1]
        Rn = Ro[:-s-1]
        if x3 == '*':
            if x2=='r':
                Ln = Lo[:-1]+'r'*s+'rd'
                pbppL[p+1] = pbppL[p+1][:-1]+'c'
            else:
                Ln = Lo[:-1]+'r'*s+'cd'
        else:
            x0= getz(Lo,-2,'')
            if x0 == 'c':
                Ln = Lo[:-2]+'r'*(s+1)+'cd'
            else:
                Ln = Lo[:-1]+'r'*(s+1)+Lo[-1]
        if p != 0:
            LLn = pbppL[p-1]
            LRn = pbppR[p-1]
            y0, y2  = Ln[-2], Ln[-1]
            y1 = LLn[len(Ln)-1]
            if (y1,y2) == ('r','r'):
                LLn = LLn[:len(Ln)-2]+'rr'+LLn[len(Ln):]
                LRn = LRn[:len(Ln)-2]+'ss'+LRn[len(Ln):]
                Ln = Ln[:len(Ln)-2]+'cd'
            elif (y1,y2) == ('c','r'):
                LLn = LLn[:len(Ln)-2]+'rc'+LLn[len(Ln):]
                LRn = LRn[:len(Ln)-2]+'ss'+LRn[len(Ln):]
                Ln = Ln[:len(Ln)-2]+'cd'
            elif (y1,y2) == ('d','r'):
                LLn = LLn[:len(Ln)-2]+'rd'+LLn[len(Ln):]
                LRn = LRn[:len(Ln)-2]+'ss'+LRn[len(Ln):]
                Ln = Ln[:len(Ln)-2]+'cd'
            elif (y1,y2) == ('d','c'):
                LLn = LLn[:len(Ln)-2]+'cd'+LLn[len(Ln):]
                LRn = LRn[:len(Ln)-2]+'ss'+LRn[len(Ln):]
                Ln = Ln[:len(Ln)-2]+'cd'
            pbppL[p-1]=LLn
            pbppR[p-1]=LRn
        pbppL[p]=Ln
        pbppR[p]=Rn
        res = (pbppL, pbppR)
    if not verify_drc(res,rtype=rtype):
        str_dgms(res)
        raise ValueError('Result in wrong PBP')
    return reg_drc(res)

def twistdown(pbplist,PP,rtype):
    p = min(PP, default=-1)
    downpp = frozenset(PP - set([p]))
    if p == -1:
        return frozenset(pbplist),downpp
    RES = frozenset(twistpbpdown(pbp,p,rtype) for pbp in pbplist)
    return RES,downpp


def Jind(ssym, r):
    """
    Not been implemented
    """
    pass


def S_Wrepn_B(part):
    """
    From special orbit to special representations of the Weyl group of type B
    """
    
    part     = [x for x in part if x!=0]
    a, res   = divmod(len(part),2)
    if res == 0:
        part = part+[0]
    part.sort()
    # Last columne must be odd
    assert(part[-1]%2 == 1)
    # C_2i and C_{2i+1} must have same parity 
    assert(not any([(part[2*i]-part[2*i+1])%2 for i in range(a)]))
    """
    e = 0 or 1
    C_{2i}     = 2 c_{2i} +e,       ==> c_{2i} = (C_{2i}-e)/2 =  C_{2i}//2
    C_{2i+1}   = 2 c_{2i+1} -e      ==> c_{2i+1} = (C_{2i+1}+e)/2 = (C_{2i+1}+1)//2
    """
    tauL = [(part[2*i-1]+1)//2 for i in range(1,a+1)]
    tauR = [part[2*i]//2 for i in range(a+1)]
    return (tauL,tauR)

    
def S_Wrepns_B(tau):
    """
    Type B
    Special representation ot set of representation in 
    coherent continuations. 
    the correct formula is 
    (c_{2i+1},c_{2i})<--> (c_{2i},c_{2i+1})
    
    We assume tauL and tauR are arranged in incresing order
    """
    tauL,tauR     = tau
    # tauL and tauR must have length a and a+1 respectively
    a             = len(tauL)
    assert(a +1 == len(tauR))
    tauL,tauR     = sorted(tauL), sorted(tauR) 
    cidxs         = [i for i in range(a) if tauL[i]!=tauR[i]]
    Atau          = []
    for k in range(len(cidxs)+1):
        for oidxs in itertools.combinations(cidxs,k):
            tauLL = [tauR[i] if i in oidxs else tauL[i] for i in range(a)]
            tauRR = [tauL[i] if i in oidxs else tauR[i] for i in range(a)]+[tauR[a]]
            Atau.append(reg_tau((tauLL,tauRR)))
    return Atau
        
    
def S_Wrepn_M(part):
    """
    From special orbit to special representations of the Weyl group of type M
    """
    part     = [x for x in part if x!=0]
    a, res   = divmod(len(part),2)
    # Must have even number of columns
    assert(res == 0)
    part.sort()
    # Last columne must be odd
    # C_2i and C_{2i+1} must have same parity 
    assert(not any([(part[2*i]-part[2*i+1])%2 for i in range(a)]))
    tauL = [(part[2*i+1]+1)//2 for i in range(a)]
    tauR = [part[2*i]//2 for i in range(a)]
    return (tauL,tauR)

    
def S_Wrepns_M(tau):
    """
    Type M
    Special representation ot set of representation in 
    coherent continuations. 
    the correct formula is 
    (c_{2i+1},c_{2i})<--> (c_{2i},c_{2i+1})
    
    We assume tauL and tauR are arranged in incresing order
    """
    tauL,tauR     = tau
    # tauL and tauR must have length a and a+1 respectively
    a             = len(tauL)
    assert(a == len(tauR))
    tauL,tauR     = sorted(tauL), sorted(tauR) 
    cidxs         = [i for i in range(a) if tauL[i]!=tauR[i]]
    Atau          = []
    for k in range(len(cidxs)+1):
        for oidxs in itertools.combinations(cidxs,k):
            tauLL = [tauR[i] if i in oidxs else tauL[i] for i in range(a)]
            tauRR = [tauL[i] if i in oidxs else tauR[i] for i in range(a)]
            Atau.append(reg_tau((tauLL,tauRR)))
    return Atau
        

"""
Construct specail and nonspecial Wrepns from a type C partition.
"""

def S_Wrepn_C(part):
    """
    From special orbit to special representations of the Weyl group
    """
    part = [x for x in part if x!=0]
    a, res = divmod(len(part),2)
    if res == 0:
        part.append(0)
    part.sort()
    # part[0] must be even
    assert(part[0]%2==0) # parity condition
    # C_{2i} and C_{2i-1} must have same parity 
    assert(not any([(part[2*i]-part[2*i-1])%2 for i in range(1,a+1)]))
    tauL = [(part[2*i-1]+1)//2 for i in range(1,a+1)]
    tauR = [part[2*i]//2 for i in range(a+1)]
    return (tauL,tauR)


def S_Wrepn_BC(part):
    """
    From special orbit to special representations of the Weyl group of
    type B and type C
    Not check the specialness of the partition
    """
    part     = [x for x in part if x!=0]
    a, res   = divmod(len(part),2)
    if res == 0:
        part = part+[0]
    part.sort()
    tauL = [(part[2*i-1]+1)//2 for i in range(1,a+1)]
    tauR = [part[2*i]//2 for i in range(a+1)]
    return (tauL,tauR)

def S_Wrepns_C(tau):
    """
    Type C
    Special representation ot set of representation in 
    coherent continuations. 
    the correct formula is 
    (c_2i,c_{2i-1})<--> (c_{2i-1}-1,c_2i+1)
    """
    tauL,tauR = tau
    # tauL and tauR must have length a and a+1 respectively
    a = len(tauL)
    assert(a +1 == len(tauR))
    tauL,tauR = sorted(tauL), sorted(tauR) 
    cidxs = [ i for i in range(a) if tauL[i]!=tauR[i+1]+1]
    Atau = []
    for k in range(len(cidxs)+1):
        for oidxs in itertools.combinations(cidxs,k):
            tauLL= [tauR[i+1]+1 if i in oidxs else tauL[i] for i in range(a)]
            tauRR= [tauR[0]]+[tauL[i]-1 if i in oidxs else tauR[i+1] for i in range(a)]
            Atau.append(reg_tau((tauLL,tauRR)))
    return Atau


def S_Wrepn_D(part):
    """
    From type D special orbit to special representations of the Weyl group
    """
    part = [x for x in part if x!=0]
    ll = len(part)
    part.sort()
    a, res = divmod(ll,2) 
    if res == 1:
        part=[0]+part
        a = a+1
    #print(C,a)
    # The last entry C_{2a-1} must be even
    assert(part[-1]%2 ==0)
    tauL = [(part[2*i+1]+1)//2 for i in range(a)]
    tauR = [part[2*i]//2 for i in range(a)]
    return (tauL,tauR)


def S_Wrepns_D(tau):
    """
    Type D
    Special representation ot set of representation in 
    coherent continuations. 
    the formula is 
    (c_{2i},c_{2i-1})<--> (c_{2i-1}-1,c_{2i}+1)
    
    We assume tauL and tauR are arranged in incresing order
    """
    
    tauL, tauR = tau
    assert(len(tauL) == len(tauR))
    a = len(tauL)
    tauL,tauR = sorted(tauL), sorted(tauR) 
    # tauL[i-1] = c_{2i-1}, tauR[i] = c_{2i}
    cidxs = [i for i in range(1,a) if tauL[i-1]!=tauR[i]+1]
    Atau = []
    for k in range(len(cidxs)+1):
        for oidxs in itertools.combinations(cidxs,k):
            tauLL= [tauR[i]+1 if i in oidxs else tauL[i-1] for i in range(1,a)]+[tauL[a-1]]
            tauRR= [tauR[0]]+[tauL[i-1]-1 if i in oidxs else tauR[i] for i in range(1,a)]
            Atau.append(reg_tau((tauLL,tauRR)))
    return Atau



DTSpringer = {
    'B': (S_Wrepn_B,S_Wrepns_B),
    'C': (S_Wrepn_C,S_Wrepns_C),
    'D': (S_Wrepn_D,S_Wrepns_D),
    'M': (S_Wrepn_M,S_Wrepns_M),
}

def dualpart2WrepnA(part, rtype):
    """
    We do not assum the orbit is purly even.
    """
    # gpart is always special
    gpart  = dualBVW(part,rtype,partrc='c')
    srepn, grepn = DTSpringer[rtype]
    RES = tuple(reg_W_repn(tau) for tau in grepn(srepn(gpart)))
    return RES

def frow_col_list(part):
   """
   This function return a list of list records the group of final rows
   """ 
   lidx = {}
   for i,l in enumerate(part):
       lidx[l] = lidx.get(l,[])+[i]
   return list(lidx.values())    

def yield_cindex(lidxs):
        """
        lidxs is a list of list of  indexes
        [[a_11, ..., a_1k],[a_21,..., a_2l], ..., [...]]
        the function yield an iterator return 
        a list of indexes [i_1, ..., i_k]
        where consists last k_i elements in the i-th list
        """
        N = 0
        nlst = len(lidxs) # Length of the list 
        llens = [len(lt) for lt in lidxs]
        cidx = [0 for lt in lidxs]
        # yields the first index
        idx = [x for j, lt in enumerate(lidxs) for x in lt]
        yield idx
        while True:
            for i in reversed(range(nlst)):
               if cidx[i] != llens[i]:
                   break
            else:
                return
            cidx[i] += 1
            cidx = cidx[:i+1]+[0]*(nlst-i-1)
            idx = [x for j, lt in enumerate(lidxs) for x in lt[cidx[j]:llens[j]] ]
            #print('#%d: %s'%(N,idx))
            yield idx


def frow_data(part):
    #assert(len(part)>0)
    Rind = [part[i]-part[i+1] for i in range(len(part)-1)]+part[-1:]
    return Rind

def yield_r_del(Rind):
        """
        lidxs is a list of list of  numbers 
        [c_0, ..., c_k]
        the function yield an iterator return 
        a list of numbers [r_0, ..., r_k]
        such that r_i <= c_i
        """
        N = 0
        nlst = len(Rind) # Length of the list 
        ridx = [r for r in Rind]
        # yields the first index
        yield ridx
        while True:
            for i in range(nlst):
                if ridx[i] >0:
                   break
            else:
                return
            ridx = Rind[:i]+[ridx[i]-1]+ridx[i+1:]
            yield ridx



IDdgm = lambda x: x
SWdgm = lambda x: (x[1],x[0])


def fill_rdot(tau, reststeps=[], sym='s', LRdgm=IDdgm, simp_Wrepn=True):
    """
    Here the Young diagram is parameterized by columns 
    ([tauL_0, ...], [tauR_0, ...])
    put symbol ('s') one the left diagram, 
    and then fill * on left and right diagrams.
    cL ncL        cR
    *  *          *  *
    *  *          *  *
    *  *          *  *
    *             *
    r
    
    Note that we always have tauL[i] >= tauR[i] >= tauL[i-1] 
    """
    if simp_Wrepn:
        tau = simp_W_repn(tau)
    if tau is not None: 
        tauL,tauR = LRdgm(tau)
        drcL, drcR = [],[]
        cols = max(len(tauL),len(tauR))
        for i in range(cols):
            cL, cR = getz(tauL,i,0), getz(tauR,i,0)
            ncL = getz(tauL,i+1,0)
            if cL >= cR and cL-cR <= cL - ncL:
                bul = '*'*cR
                drcR.append(bul)
                drcL.append(bul+sym*(cL-cR))
            else:
                return
        yield LRdgm((tuple(drcL),tuple(drcR)))

def fill_r(tau, reststeps=[], sym='r', LRdgm=IDdgm):
    """
    Here the Young diagram is parameterized by columns 
    ([tauL_0, ...], [tauR_0, ...])
    put r at the left diagram and then do the reststeps 
    """
    rrsteps = reststeps[1:]
    rfun, rparam = reststeps[0]
    tau = simp_W_repn(tau) 
    if tau is not None: 
        # fillL=False then switch left and right diagrams
        tauL,tauR = LRdgm(tau)
        rL = len(tauL)
        # If tauL is an empty list,
        #    yield_r_del still will yield an empty list
        #if rL == 0:
        #    tauL, rL = [0], 1
        frow_lst = frow_data(tauL)
        for rdel in yield_r_del(frow_lst):
            tauLL = [tauL[i] - rdel[i] for i in range(rL)]
            for drcL, drcR in rfun((tauLL, tauR), rrsteps, *rparam):
                drcLL = tuple(getz(drcL,i,'')+(sym*rdel[i])
                              for i in range(rL)) 
                yield LRdgm((drcLL, drcR))


def fill_c(tau, reststeps=[], sym = 'c', LRdgm = IDdgm):
    """
    fill c in the longest column
    """
    rrsteps = reststeps[1:]
    rfun, rparam = reststeps[0]
    tau = simp_W_repn(tau)
    if tau is not None: 
        tauL,tauR = LRdgm(tau)
        rL = len(tauL)
        # if rtauL is empty, yield_cindex still will yeild an empty list 
        # if rL == 0:
        #    tauL, rL = [0], 1
        frow_lst = frow_col_list(tauL)
        for cidx in yield_cindex(frow_lst):
            tauLL = copy(tauL)
            for i in cidx:
                tauLL[i] -=1
            for drcL,drcR in rfun((tauLL, tauR), rrsteps, *rparam):
                drcL = list(drcL)+['']*(rL-len(drcL))
                for i in cidx:
                    drcL[i] = getz(drcL,i,'')+sym
                yield LRdgm((tuple(drcL),drcR))



def reg_tau(tau):
    tauL,tauR=tau
    tauL = sorted([x for x in tauL if x!=0],reverse=True)
    tauR = sorted([x for x in tauR if x!=0],reverse=True)
    return (tauL,tauR)



def countdrcform(drc):
    dot = sum(c.count('*') for c in itertools.chain(*drc))
    r = sum(c.count('r') for c in itertools.chain(*drc))
    s = sum(c.count('s') for c in itertools.chain(*drc))
    c = sum(c.count('c') for c in itertools.chain(*drc))
    d = sum(c.count('d') for c in itertools.chain(*drc))
    return (dot, r, s, c, d)
    

def gp_form_D(drc):
    #print(drc)
    cplx, cpt1, cpt2, real1, real2  = countdrcform(drc)
    p, q = cplx+real1+real2+cpt1*2, cplx+real1+real2+cpt2*2
    return (p,q)

def dual_form_D(drc):
    cplx, real1, real2, cpt1, cpt2  = countdrcform(drc)
    dp, dq = cplx+real1+real2+cpt1*2, cplx+real1+real2+cpt2*2
    return (dp,dq)


def gp_form_C(drc):
    return sum(len(c) for c in itertools.chain(*drc))

gp_form_M = gp_form_C

def dual_form_C(drc):
    cplx, real1, real2, cpt1, cpt2  = countdrcform(drc)
    p, q = cplx+real1+real2+cpt1*2+1, cplx+real1+real2+cpt2*2
    return (p,q)


def gp_form_B(drc):
    cplx, cpt1, cpt2, real1, real2  = countdrcform(drc)
    dp, dq = cplx+real1+real2+cpt1*2, cplx+real1+real2+cpt2*2
    if dp % 2 == 1:
        dp = dp + 1
    else:
        dq = dq + 1
    return (dp,dq)

def dual_form_B(drc):
    cplx, real1, real2, cpt1, cpt2  = countdrcform(drc)
    dp, dq = cplx+real1+real2+cpt1*2+1, cplx+real1+real2+cpt2*2
    return (dp,dq)

steps_D  =[
    (fill_c, ('d',)),
    (fill_c, ('c',)),
    (fill_r, ('r',)),
    (fill_rdot, ('s',))]

steps_C  =[
    (fill_c, ('d',)),
    (fill_c, ('c',)),
    (fill_r, ('s', SWdgm)),
    (fill_rdot, ('r', SWdgm))]

steps_B  =[
    (fill_c, ('d', SWdgm)),
    (fill_c, ('c', SWdgm)),
    (fill_r, ('r', SWdgm)),
    (fill_rdot, ('s', ))]

steps_M  =[
    (fill_c, ('d', SWdgm)),
    (fill_c, ('c', SWdgm)),
    (fill_r, ('r', SWdgm)),
    (fill_rdot, ('s', SWdgm))]

def drc_form_Sp(drc):
    return 2*gp_form_C(drc)

DRCRule = {
    'D': (S_Wrepn_D, S_Wrepns_D, steps_D,
          r'SO(%d,%d)', gp_form_D, r'SO(%d,%d)', dual_form_D),
    'C': (S_Wrepn_C, S_Wrepns_C, steps_C,
          r'Sp(%d)', drc_form_Sp, r'SO(%d,%d)', dual_form_C),
    'B': (S_Wrepn_B, S_Wrepns_B, steps_B,
          r'SO(%d,%d)', gp_form_B, r'SO(%d,%d)', dual_form_B),
    'M': (S_Wrepn_M, S_Wrepns_M, steps_M,
          r'Mp(%d)', drc_form_Sp, r'Mp(%d)', drc_form_Sp),
    }


def part2drc(partition, rtype = 'D',
                report = True,printdig=False, getlist=False,print_Wrepn=False):
    """
    print the dcr_diag attached to Nilpotent orbit of type D
    partition: = [C_{2a-1}>=C_{2a-2}... >=C_0>=0] is the list of column lengths of 
                  a type C nilpotent orbits. 
    """
    assert(rtype in DRCRule)
    spWrepn, AWrepns, steps, strgpform, gpform, strdualform, dualform = DRCRule[rtype]
    
    tau = spWrepn(partition)
    Atau = AWrepns(tau)
    if report:
        print("Type %s partition: %s"%(rtype,partition))
    if print_Wrepn:
        print("List of relevent Weyl group representations")
        print(Atau)

    ffun, fparam = steps[0] 

    ADRC = []
    for tau in Atau:
        ADRC.append([drc for drc in ffun(tau, steps[1:], *fparam)])
    print([len(drctau) for drctau in ADRC])
    Adrc = [drc for drc in chain(*ADRC)]
    #print(Adrc)
    if report:
        print("Number of drc diagrams: %d"%len(Adrc))
    if printdig:
        for drc in Adrc:
            drc = reg_drc(drc)
            print("%s"%str_dgms(drc))
            print("form is %s, dual form is %s\n"
                  % (strgpform%gpform(drc), strdualform%dualform(drc)))
    return Adrc


DRCRule = {
    'D': (S_Wrepn_D, S_Wrepns_D, steps_D,
          r'SO(%d,%d)', gp_form_D, r'SO(%d,%d)', dual_form_D),
    'C': (S_Wrepn_C, S_Wrepns_C, steps_C,
          r'Sp(%d)', drc_form_Sp, r'SO(%d,%d)', dual_form_C),
    'B': (S_Wrepn_B, S_Wrepns_B, steps_B,
          r'SO(%d,%d)', gp_form_B, r'SO(%d,%d)', dual_form_B),
    'M': (S_Wrepn_M, S_Wrepns_M, steps_M,
          r'Mp(%d)', drc_form_Sp, r'Mp(%d)', drc_form_Sp),
    }


GPSIGN = {
    'D': gp_form_D,
    'B': gp_form_B,
    'C': gp_form_C,
    'M': gp_form_M,
}


def count_signs(ldrc,rtype):
    count_fun = lambda drc: GPSIGN[rtype](drc)
    DD = dict()
    for drc in ldrc:
        sgn = count_fun(drc)
        DD[sgn] = DD.get(sgn,0)+1
    return DD

def dpart2drc(dpart, rtype = 'D',
                report = True,printdig=False, getlist=True,print_Wrepn=False):
    """
    print the dcr_diag attached to Nilpotent orbit of type D
    partition: = [C_{2a-1}>=C_{2a-2}... >=C_0>=0] is the list of column lengths of
                  a type C nilpotent orbits.
    """
    assert(rtype in DRCRule)
    spWrepn, AWrepns, steps, strgpform, gpform, strdualform, dualform = DRCRule[rtype]

    Atau = dualpart2Wrepn(dpart,rtype)

    if report:
        print("Type %s dual-partition: %s"%(rtype,dpart))
    if print_Wrepn:
        print("List of relevent Weyl group representations")
        print(Atau)

    ffun, fparam = steps[0]

    ADRC = dict()
    for tau in Atau:
        ADRC[tau] = [drc for drc in ffun(tau, steps[1:], *fparam)]
    Adrc = [drc for drc in chain(*ADRC.values())]
    #print(Adrc)
    if report:
        print([(tau,len(drctau)) for tau, drctau in ADRC.items()])
        Asgns = dict()
        for tau,drctau in ADRC.items():
            #print(drctau)
            Asgns[tau] = count_signs(drctau,rtype)
        #print(Asgns)
        sgnkeys = set()
        for dsigns in Asgns.values():
            sgnkeys.update(set(dsigns.keys()))

        ## Print the result
        sgnkeys = [k for k in sgnkeys]
        tb = Table(" "*20,*[str(k) for k in sgnkeys],min_width=200, show_lines=True)
        for tau, dsigns in Asgns.items():
            tb.add_row(str(tau), *[str(dsigns.get(k,0)) for k in sgnkeys])
        print(tb)


        #print(sgnkeys)
        #print("\t".join([str(k) for k in sgnkeys]))
            #print(tau)
        print("Number of drc diagrams: %d"%len(Adrc))
    if printdig:
        for drc in Adrc:
            drc = reg_drc(drc)
            print("%s"%str_dgms(drc))
            print("form is %s, dual form is %s\n"
                  % (strgpform%gpform(drc), strdualform%dualform(drc)))

    if getlist:
        return Adrc #= [drc for drc in chain(*ADRC.values())]
    else:
        return ADRC


PBPRULES = {
    'D': (steps_D,
          r'SO(%d,%d)', gp_form_D, r'SO(%d,%d)', dual_form_D),
    'C': (steps_C,
          r'Sp(%d)', drc_form_Sp, r'SO(%d,%d)', dual_form_C),
    'B': (steps_B,
          r'SO(%d,%d)', gp_form_B, r'SO(%d,%d)', dual_form_B),
    'M': (steps_M,
          r'Mp(%d)', drc_form_Sp, r'Mp(%d)', drc_form_Sp),
    }


def dpart2pbp(dpart, rtype = 'D',
                report = True,printdig=False, getlist=False,print_Wrepn=False):
    """
    print the dcr_diag attached to Nilpotent orbit of type D
    partition: = [C_{2a-1}>=C_{2a-2}... >=C_0>=0] is the list of column lengths of
                  a type C nilpotent orbits.
    """
    assert(rtype in DRCRule)
    steps, strgpform, gpform, strdualform, dualform = PBPRULES[rtype]

    Atau = springer_part2family(dpart,rtype)

    if report:
        print("Type %s partition: %s"%(rtype,dpart))
    if print_Wrepn:
        print("List of relevent Weyl group representations")
        print(Atau)

    ffun, fparam = steps[0]

    ADRC = []
    for tau in Atau:
        ADRC.append([drc for drc in ffun(tau, steps[1:], *fparam)])
    print([len(drctau) for drctau in ADRC])
    Adrc = [drc for drc in chain(*ADRC)]
    #print(Adrc)
    if report:
        print("Number of drc diagrams: %d"%len(Adrc))
    if printdig:
        for drc in Adrc:
            drc = reg_drc(drc)
            print("%s"%str_dgms(drc))
            print("form is %s, dual form is %s\n"
                  % (strgpform%gpform(drc), strdualform%dualform(drc)))
    return Adrc

# def sort_sign(ADRC,rtype='D'):
#     dsgn = dict()
#     for drc in ADRC:
#         sgn =

def Wrepn2pbps(tau,rtype='D'):
    """
    generate the dcr_diag attached to Weyl group representation orbit of type rtype
    """
    assert(rtype in DRCRule)
    spWrepn, AWrepns, steps, strgpform, gpform, strdualform, dualform = DRCRule[rtype]
    ffun, fparam = steps[0]
    Adrc = ffun(tau, steps[1:], *fparam)
    return Adrc

Wrepn2drcs=Wrepn2pbps

def count_dgms_D_forms(Adrc):
    return count_signs(Adrc, form_D)


def count_LS_D_forms(LS):
    return count_signs(LS, sign_LS)


def sign_LS(ls):
    sgnls = set(_sign_ILS(ils) for ils in ls)
    assert(len(sgnls) == 1)
    return sgnls.pop()


def compare_drc(DRCL1, DRCL2):
    DRCL1 = set(reg_drc(drc) for drc in DRCL1)
    DRCL2 = set(reg_drc(drc) for drc in DRCL2)
    return (DRCL1-DRCL2, DRCL2-DRCL1)

def compare_sign(Adrc, LS):
    sgnDRC = count_dgms_D_forms(Adrc)
    sgnLS = count_LS_D_forms(LS)
    keys = {*sgnDRC.keys(), *sgnLS.keys()}
    Esgns = dict()
    for k in keys:
        ndrc, nls = sgnDRC.get(k, 0), sgnLS.get(k, 0)
        if 2*ndrc != nls:
            Esgns[k] = 2*ndrc-nls
    return Esgns





def str_dgms(drc):
    """
    Format of drc:
    drc = (drcL,drcR)
    drcL and drcR are string tuples
    drcL = (cl_1, ..., cl_k),
        each cl_i represents
        the symbol of a column
    """
    drcL,drcR = drc
    cL,cR = len(drcL),len(drcR)
    r = max(len(getz(drcL,0,'')),len(getz(drcR,0,'')))
    S = []
    for i in range(r):
        ll = [getz(cl,i,' ') for cl in drcL]
        rr = [getz(cr,i,' ') for cr in drcR]
        S.append(''.join(ll)+'|'+''.join(rr))
    s = '\n'.join(S)
    s = s.replace('*','.')
    return s   
            
def print_drcs(DRCS):
    for drc in DRCS:
        print('\n-----------\n%s\n'%str_dgms(drc))

def test_young_dg(dg):
    return all(len(getz(dg,i,''))>= len(getz(dg,i+1,'')) 
               for i in range(len(dg)))

def test_young_drc(drc):
    drcL, drcR = drc
    return test_young_dg(drcL) and test_young_dg(drcR)

def test_bullets_drc(drc):
    drcL, drcR = drc
    for i in range(max(len(drcL),len(drcR))):
        cL, cR = getz(drcL, i, ''), getz(drcR, i, '')
        nL, nR = cL.count('*'), cR.count('*')
        if  (len(cL),len(cR)) != (nL, nR) or len(cL) != len(cR):
            return False
    return True
    
def remove_tail_letter(dg,l,onerow=False):
    ddg = []
    for col in dg:
        dcol = col.rstrip(l)
        if onerow and len(col)-len(dcol)>1:
            return None
        ddg.append(dcol)
    return tuple(ddg)

            
def verify_drc(drc, rtype='C'):
    if rtype == 'C':
        drcL, drcR = drc
        if test_young_dg(drcL) is False or test_young_dg(drcR) is False:
            return False
        cdrcL = remove_tail_letter(drcL,'d',onerow=True)
        if cdrcL is None or test_young_dg(cdrcL) is False:
            return False
        ccdrcL = remove_tail_letter(cdrcL,'c',onerow=True)
        if ccdrcL is None or test_young_dg(ccdrcL) == False:
            return False
        rccdrcL = remove_tail_letter(ccdrcL,'r')
        rdrcR = remove_tail_letter(drcR,'s')
        if rccdrcL is None or test_young_dg(rccdrcL) is False or \
            rdrcR is None or test_young_dg(rdrcR) is False or\
            test_bullets_drc((rccdrcL,rdrcR)) is False:
            return False
    elif rtype == 'D':
        drcL, drcR = drc
        if test_young_dg(drcL) is False or test_young_dg(drcR) is False:
            return False
        cdrcL = remove_tail_letter(drcL,'d',onerow=True)
        if cdrcL is None or test_young_dg(cdrcL) is False:
            return False
        ccdrcL = remove_tail_letter(cdrcL,'c',onerow=True)
        if ccdrcL is None or \
            test_young_dg(cdrcL) == False:
            return False
        rccdrcL = remove_tail_letter(ccdrcL,'r')
        if rccdrcL is None:
            return False
        srccdrcL = remove_tail_letter(rccdrcL,'s')
        if srccdrcL is None or \
            test_bullets_drc((srccdrcL,drcR)) is False:
            return False  
    return True

def reg_drc(drc):
    if drc is None: return None
    drcL, drcR = drc
    drcL = tuple(x for x in drcL if len(x)> 0)
    drcR = tuple(x for x in drcR if len(x)> 0)
    return (drcL, drcR)
    


