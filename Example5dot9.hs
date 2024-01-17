---------------------------------------------------------------
-- This module implements the objects defined in Example 5.9 --
---------------------------------------------------------------


module Example5dot9 where

import CompositionFunction 
import DataTypes


-- ========== EXAMPLE 5.9 ===========

-- participants in the example -------------------------

p = (Participant "p")
r = (Participant "r")
s = (Participant "s")
q = (Participant "q")
nh = (Participant "h")
nv = (Participant "v")
nw = (Participant "w")

--  interactions in the example ----------------------------

htop = Interaction (Participant "h") (Participant "p")
ptoh = Interaction (Participant "p") (Participant "h")
stov = Interaction (Participant "s") (Participant "v")
wtor = Interaction (Participant "w") (Participant "r")
rtow = Interaction (Participant "r") (Participant "w")

---- messages in the example ---------------------------

reactn = (Message "reactn")
img    = (Message "img")
start  = (Message "start")
halt   = (Message "halt")
go     = (Message "go")
stop   = (Message "stop")

-- global types in the example -------------------

g1pp = MkGT ptoh [((Message "reactn"),(MkGT htop [((Message "img"),g1)]))]
g1p = MkGT htop [((Message "img"),g1pp),((Message "halt"),End)]

g1  = MkGT htop [((Message "start"),g1p)]
g2  = MkGT stov [((Message "img"),g2),((Message "halt"),g2)]
g3 = MkGT wtor [((Message "reactn"),(MkGT rtow [((Message "img"),g3)]))]

-- the processes in the example ------------

h3 = (MkOutput p [(img,Inact)])
h2 = (Mkinput p [(reactn,h3)])
h1 = (MkOutput p [(img,h2),(halt,Inact)])
h  = (MkOutput p [(start,h1)])

v  = (Mkinput s [(img,v),(halt,v)])

w1 = (Mkinput r [(img,w)])
w  = (MkOutput r [(reactn,w1)])

-- -------- the compliance derivation in the example -------------------

der1 = (Comp0 (Judgment Inact v w)) -- applyComp0 v w
der2 = (CompIOR [(CompOIR [der] (Judgment h3 v w1))] (Judgment h2 v w))
der3 = (CompOIL [der2,der1] (Judgment h1 v w))

der = (CompOIA [der3] (Judgment h v w))


-- The (infinite) global type that can be obtained by composing g1, g2 and g3 is hence
--                        (g der g1 g2 g3 nh nv nw)
-- whose cut at level, say, 10 can be obtained by evaluating
--            prune 10 (g der g1 g2 g3 nh nv nw)
-- getting
-- h->p : start. s->v : {
--                       img. v->h : img. h->p : img. p->h : reactn. h->w : reactn. w->r : reactn. r->w : img. w->h : img. h->p : img. ETC.,
--                       halt. v->h : halt. h->p : halt. End}


