---------------------------------------------------------------
-- This module implements the objects defined in Section 6 --
---------------------------------------------------------------


module ExampleSect6 where

import FunctionDefinition
import DataTypes


-- participants in the example -------------------------

np = (Participant "p")
nr = (Participant "r")
ns = (Participant "s")
nq = (Participant "q")
nh = (Participant "h")
nv = (Participant "v")
nw = (Participant "w")

--  interactions in the example ----------------------------

htop = Interaction nh np
ptoh = Interaction np nh
stov = Interaction ns nv
vtos = Interaction nv ns
wtor = Interaction nw nr
rtow = Interaction nr nw

---- messages in the example ---------------------------
terep = (Message "te-rep")
tereq = (Message "te-req")
tefail = (Message "te-fail")
hufail = (Message "hu-fail")
hurep = (Message "hu-rep")
hureq = (Message "hu-req")
prreq = (Message "pr-req")
prrep = (Message "pr-rep")
prfail = (Message "pr-fail")
presval = (Message "pres-val")
presvalreq = (Message "pres-val-req")
fixtips = (Message "fix-tips")
ping = (Message "ping")
pong = (Message "pong")
rebpars = (Message "reb-pars")


-- global types in the example -------------------

gp3  = MkGT ptoh [(pong,gms)]
gp2  = MkGT ptoh [(ping,gms3)]
gp1  = MkGT htop [(prrep,gp2),(prfail,End)]
gp   = MkGT ptoh [(prreq,gp1)]
gms3 = (MkGT htop [(hurep,gp),(hufail,End)])
gms2 = MkGT ptoh [(hureq,gms3)]
gms1 = MkGT htop [(terep,gms2),(tefail,End)]

gms  = MkGT ptoh [(tereq,gms1)]

ghs3 = MkGT stov [(pong,ghs)]
ghs2 = MkGT stov [(presval,ghs)] 
ghs4 = MkGT stov [(fixtips,ghs)]
ghs1 = MkGT stov [(hurep,ghs),(hufail,ghs4)]

ghs = MkGT vtos [(hureq,ghs1),(presvalreq,ghs2),(ping,ghs3)]

gps2 = MkGT rtow [(pong,gps)]
gps3 = MkGT rtow [(rebpars,gps)] 
gps1 = MkGT rtow [(prrep,gps),(prfail,gps3)]

gps = MkGT wtor [(prreq,gps1),(ping,gps2)]


-- the processes in the example ------------

ph7  = MkOutput np [(pong,ph)]
ph6  = MkInput np [(ping,ph7)]
ph5  = MkOutput np [(prrep,ph6),(prfail,Inact)]
ph4  = MkInput np [(prreq,ph5)]
ph3  = MkOutput np [(hurep,ph4),(hufail,Inact)]
ph2  = MkInput np [(hureq,ph3)]
ph1  = MkOutput np [(terep,ph2),(tefail,Inact)]

ph  = MkInput np [(tereq,ph1)]   -- The process H in the example

pp7  = MkInput nh [(pong,pp)]
pp6  = MkOutput nh [(ping,pp7)]
pp5  = MkInput nh [(prrep,pp6),(prfail,Inact)]
pp4  = MkOutput nh [(prreq,pp5)]
pp3  = MkInput nh [(hurep,pp4),(hufail,Inact)]
pp2  = MkOutput nh [(hureq,pp3)]
pp1  = MkInput nh [(terep,pp2),(tefail,Inact)]

pp  = MkOutput nh [(tereq,pp1)] -- The process P in the example

pv2  = MkInput ns [(fixtips,pv)]
pv1  = MkInput ns [(hurep,pv),(hufail,pv2)]

-- The process V in the example
pv  = MkOutput ns [(hureq,pv1),(presvalreq,(MkInput ns [(presval,pv)])),(ping,(MkInput ns [(pong,pv)]))] 

ps4  = MkOutput nv [(fixtips,ps)]
ps3  = MkOutput ns [(pong,ps)]
ps2  = MkOutput nv [(presval,ps)]
ps1  = MkOutput nv [(hurep,ps),(hufail,ps4)]

ps  = MkInput nv [(hureq,ps1),(presvalreq,ps2),(ping,ps3)]  -- The process S in the example

pw2  = MkInput nr [(rebpars,Inact)] 
pw1  = MkInput nr [(prrep,pw),(prfail,pw2)]

pw  = MkOutput nr [(prreq,pw1),(ping,(MkInput nr [(pong,pw)]))]  -- The process W in the example

pr3  = MkOutput nw [(rebpars,Inact)]
pr2  = MkOutput nw [(pong,pr)]
pr1  = MkOutput nw [(prrep,pr),(prfail,pr3)]

pr  = MkInput nw [(prreq,pr1),(ping,pr2)]  -- The process R in the example

-- -------- the compliance derivation in the example -------------------



dmhp9 = (CompOIL [dmhpp] (Judgment ph7 (MkInput ns [(pong,pv)]) pw))
dmhp7 = (CompIOL [dmhp9] (Judgment ph6 pv pw))
dmhp8 = (Comp0 (Judgment Inact pv pw2))
dmhp6 = (CompOIR [dmhp7,dmhp8] (Judgment ph5 pv pw1))
dmhp5 = (CompIOR [dmhp6] (Judgment ph4 pv pw)) 
dmhp10 = (Comp0 (Judgment Inact pv2 pw))
dmhp4 = (CompOIL [dmhp5,dmhp10] (Judgment ph3 pv1 pw))
dmhp2 = (CompIOL [dmhp4] (Judgment ph2 pv pw))
dmhp3 = (Comp0 (Judgment Inact pv pw))
dmhp1 = (CompOA [dmhp2, dmhp3] (Judgment ph1 pv pw))

dmhp = (CompIA [dmhp1] (Judgment ph pv pw))


dmhpp9 = (CompOIL [dmhp] (Judgment ph7 (MkInput nr [(pong,pv)]) pw))
dmhpp7 = (CompIOL [dmhpp9] (Judgment ph6 pv pw))
dmhpp8 = (Comp0 (Judgment Inact pv pw2))
dmhpp6 = (CompOIR [dmhpp7,dmhpp8] (Judgment ph5 pv pw1))
dmhpp5 = (CompIOL [dmhpp6] (Judgment ph4 pv pw))
dmhpp10 = (Comp0 (Judgment Inact pv2 pw))
dmhpp4 = (CompOIL [dmhpp5,dmhpp10] (Judgment ph3 pv1 pw))
dmhpp2 = (CompIOL [dmhpp4] (Judgment ph2 pv pw))
dmhpp3 = (Comp0 (Judgment Inact pv pw))
dmhpp1 = (CompOA [dmhpp2, dmhpp3] (Judgment ph1 pv pw))

dmhpp = (CompIA [dmhpp1] (Judgment ph pv pw))



-- The (infinite) global type that can be obtained by composing gms, ghs and gps is hence
--                        (g dmhp gms ghs gps nh nv nw)
-- whose cut at level, say, 10 can be obtained by evaluating
--            prunegt 10 (g dmhp gms ghs gps nh nv nw)
-- getting
-- p->h : te-req. h->p : {
--                        te-rep. p->h : hu-req. h->v : hu-req. v->s : hu-req. s->v : {
--                                                                             hu-rep. v->h : hu-rep. h->p : hu-rep. p->h pr-req. h->w : pr-req. ETC.,
--                                                                             hu-fail. v->h : hu-fail. h->p : hu-fail. End},
--                        te-fail. End}
--
--


