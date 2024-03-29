from rich import print
from itertools import chain, zip_longest
from copy import copy, deepcopy
from multiset import FrozenMultiset as frozenset
from .tool import *
from .drc import *
from .LS import *
from .drclift import *

# from combunipotent.tool import _simp_dec_seq

from graphviz import Digraph
from IPython.display import display, Image, SVG

def _update_tdict(tdict, tkey, fkey):
    ltype, ffkey = fkey
    if (ltype, tkey) not in tdict.get(ffkey,set()):
        tlist = tdict.get(tkey, set())
        tlist.add(fkey)
        tdict[tkey] = tlist


# RDATA records (dual type, good parity, liftfun)
RDATA= {
    'D': ('C', 0, lift_C_D),
    'C': ('D', 0, lift_D_C),
    'B': ('M', 1, lift_M_B),
    'M': ('B', 1, lift_B_M),
}


def LS_graph(tdict, part, rtype, increase=False):
    """
    tree dict
    """
    # get the rtype of pervious patten
    drtype, goodp, liftfun = RDATA[rtype]

    part = simp_dec_seq(part)
    partsize = part_size(part)
    n, res = divmod(partsize, 2)
    LS_data = getattr(LS_graph,'LS_data',dict())
    partkey = (rtype,tuple(part))
    if partkey in LS_data:
        return LS_data[partkey]
    if rtype in  ('C', 'M'):
        """
        Take a partition of type C
        part = (Ca, Cap, ..., C_1)
        If Ca is odd, Ca = Cap, we use generalized descent,
                            lift LS of type D with (Cap+1, ..., C_1)
        If Ca is even, Cap must be even, we use descent
        """
        assert(res == 0)
        if partsize == 0:
            # return the set of empty tuple
            ss = frozenset([()])
            tkey = (rtype,partsize,ss)
            tdict[tkey] = set()
            LS_data[partkey] = set([ss,])
            LS_graph.LS_data = LS_data
            return LS_data[partkey]
        else:
            Ca, Cap = part[0],getz(part, 1,0)
            if Ca % 2 == goodp:
                assert(Cap%2 == goodp)
                ppart = part[1:]
                lftsym = 'l'
            elif Ca == Cap:
                ppart = (Cap+1, *part[2:])
                lftsym = 'L'
            else:
                raise ValueError("parity error")
            ppartsize = part_size(ppart)
            S = LS_graph(tdict,ppart,drtype)
            SS = []
            for s in S:
                ss = liftfun(s,n,increase=increase)
                if len(ss) >0 :
                    ss = frozenset(ss)
                    SS.append(ss)
                    tkey = (rtype, partsize, ss)
                    fkey = (lftsym, (drtype, ppartsize,s))
                    _update_tdict(tdict,tkey,fkey)
            LS_data = getattr(LS_graph,'LS_data',dict())
            SS = set(SS)
            LS_data[partkey] =  SS
            LS_graph.LS_data=LS_data
            return SS
    elif rtype in ('D', 'B'):
        assert(res == goodp)
        if partsize == 0:
            ss = frozenset([()])
            tdict[(rtype,partsize,ss)] = set()
            # return the set of empty tuple
            LS_data[partkey] = set([ss,])
            LS_graph.LS_data = LS_data
            return LS_data[partkey]
            return set([ss])
        else:
            ppart = part[1:]
            ppartsize = part_size(ppart)
            S = LS_graph(tdict, ppart, drtype,increase=increase)
            # Lift trivial system first
            SS = []
            for i in range(partsize+1):
                for s in S:
                    ss = liftfun(s, i, partsize-i, increase=increase)
                    if len(ss) > 0 :
                        ss = frozenset(ss)
                        SS.append(ss)
                        tkey = (rtype,partsize,ss) # target key
                        fkey = ('l', (drtype,ppartsize,s)) # from key
                        _update_tdict(tdict, tkey, fkey)
            SSS = []
            tsgns = {(1,1): 't', (1,-1):'q', (-1,1):'p', (-1,-1):'d' }
            for (tp,tn) in tsgns.keys():
                for ss in SS:
                    sss = char_twist_D(ss,(tp,tn))
                    if len(sss)>0:
                        sss = frozenset(sss)
                        SSS.append(frozenset(sss))
                        if (tp,tn) != (1,1):
                            tkey = (rtype,partsize, sss)
                            skey = (rtype,partsize, ss) # source key
                            ltype = tsgns[(tp,tn)]
                            sskey = (ltype, skey) # soruce key in tlist = (ltype, source key)
                            ttkey = (ltype, tkey) # target key in tlist = (ltype, target key)
                            #if (ltype,tkey) not in tdict.get(skey,set()):
                            _update_tdict(tdict,tkey,sskey)
                            _update_tdict(tdict,skey,ttkey)
            SSS = set(SSS)
            LS_data = getattr(LS_graph,'LS_data',dict())
            LS_data[partkey] =  SSS
            LS_graph.LS_data=LS_data
            return SSS
    else:
        raise ValueError('Wrong root system type %s'%rtype)

rtype_gp = {'C':r'Sp(%d)',
            'D':r'O(%d)',
            'M':r'Mp(%d)',
            'B':r'O(%d)',
            }

line_attr_dict = {
    'l':{
        'color':'blue',
        'tailport':'s',
        'headport':'n',
    },
    'L':{
        'color':'navy',
        'tailport':'s',
        'headport':'n',
    },
    'p':{
        'dir':'both',
        'arrowsize':'0.3',
        'color':'green',
    },
    'q':{
        'dir':'both',
        'arrowsize':'0.3',
        'color':'purple',
    },
    'd':{
        'dir':'both',
        'arrowsize':'0.3',
        'color':'red',
    },
}

def tdict_LSDRC_tograph(g, tdict, dLSDRC):
    lsets = {}
    lnodes = {}
    lgps = []  # list of complex forms of the groups
    ggp = Digraph(node_attr={'shape':'plaintext'})
    for (rtype, partsize, ss), v in tdict.items():
        #str_ss = str_LS(ss,show_sign=True)
        ## This give the horizontal line of nodes
        lsets[(rtype,partsize)]=lsets.get((rtype,partsize),[])+[ss]
        gplabel = rtype_gp[rtype]%partsize
        if gplabel not in lgps:
            lgps.append(gplabel)
            ggp.node(gplabel)
        for ltype, (crtype, cpartsize, sss)  in v:
            str_sss = str_LS(sss,show_sign=True)
            lnodes[ss] = lnodes.get(ss,[])+[(ltype, sss, str_sss)]
    for i, gplabel  in enumerate(lgps):
        if  i!=0:
            pplabel = lgps[i-1]
            ggp.edge(pplabel,gplabel)
    # plot group labels
    g.subgraph(ggp)

    # plot horizontal line of LSs of same complex group
    for (rtype,partsize), sslist in lsets.items():
        tg = Digraph(graph_attr= {'rank':'same',
                                  'rankdir':'LR',
                                  'sep':'1',
                                  'nodesep':'2',
                                  'concentrate':'false',
                                  })
        gplabel = rtype_gp[rtype]%partsize
        tg.node(gplabel,group=gplabel)
        for ss in sslist:
            str_ss = str_LS(ss,show_sign = True)
            str_ss_drc_packet= strLSpacket(ss, dLSDRC)
            label_ss = str_ss+'\n'+str_ss_drc_packet +'\n'
            label_ss = label_ss.replace('\n','\l')
            tg.node(str_ss, label=label_ss, group=gplabel,
                    fontname='Courier New',
                    #fontname='Monospace:matrix=1 .1 0',
                    #fontname='monospace',
                    fontsize='10.0',
                    labeljust='l',
                    nojustify='true')
            for ltype, sss, str_sss in lnodes.get(ss,[]):
                if ltype in ['p','q','d']:
                    tg.edge(str_sss,str_ss, **line_attr_dict[ltype])
        g.subgraph(tg)
    # plot theta lifting maps
    for ss, v in lnodes.items():
        str_ss = str_LS(ss, show_sign=True)
        for ltype, sss, str_sss in v:
            if ltype not in ['p','q','d']:
                g.edge(str_sss,str_ss,**line_attr_dict[ltype])
    return g

def _find_source(tdict, fkey, lftsym):
    skeys = [skey for slftsym, skey in tdict.get(fkey,set()) if slftsym == lftsym]
    assert(len(skeys)<=1)
    if skeys:
        return skeys[0]
    else:
        return None

def mergedicts(dicts):
    res = dict(chain(*(d.items() for d in dicts)))
    return res

def gen_lift_graph(part, rtype='C', increase=False, format='svg'):
    lDRCLS, lLSDRC=test_purelyeven(part,rtype)
    dLSDRC = mergedicts(lLSDRC)
    #print("here")

    tdict = {}
    LS_graph.LS_data=dict()
    LS_graph(tdict,part,rtype=rtype,increase=increase)
    g = Digraph(name='Lift Tree',
                filename='lift_tree',
                node_attr={'shape':'box'},
                graph_attr={'newrank':'true',
                            'concentrate':'false',
                            'compound':'true',
                            'ranksep':'1.5 equally',
                            'splines':'true',
                            'sep':'0.5',
                            'fontname':'Courier New',
                            'fontsize':'10',
                            'nojustify':'true',
                            #'dpi':'500',
            },
                engine='dot',
                format=format)
    svgg = tdict_LSDRC_tograph(g, tdict, dLSDRC)
    if svgg and format=='svg':
        svgg=SVG(svgg.render())
    return svgg
