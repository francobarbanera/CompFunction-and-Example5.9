-------------------------------------------------------------------------------
-- This module implements Processes, Global Types and Compliance derivations --
-------------------------------------------------------------------------------



module DataTypes where

-- ===== Participants, Interactions and Messages ======

data Participant =  Participant String
 deriving (Eq)

instance Show Participant where
     show (Participant s) = s


data Interaction = Interaction Participant Participant
  deriving (Eq)

instance Show Interaction where
     show (Interaction p1 p2) = (show p1)++"->"++(show p2)


data Message =  Message String
 deriving (Eq)

instance Show Message where
     show (Message s) = s



--  ==== GlobalTypes ==============

data GlobalType = End 
                 | MkGT Interaction [(Message,GlobalType)] 
                 | Cut -- represents a "pruned away" subterm (needed when showing a pruned global type) 

instance Show GlobalType where
     show gt = showd 0 gt
           where
               showd n End = "End"
               showd n Cut = "ETC."
               showd n (MkGT inter [])       = "malformed type"
               showd n (MkGT inter [(l,gt)]) = (show inter)++" : "++(show l)++". "++(showd (n+(lenint inter)+(lenmes l)+(if (n==0) then 4+(lenmes l) else 6)) gt)
               showd n (MkGT inter ls)          = (show inter)++" : {"++"\n"++(showlist (n+(lenint inter)) ls)++"}" 
               showlist n [(l,gt)]     = (blanks n)++(show l)++". "++(showd n gt)
               showlist n ((l,gt):xs)  = (blanks n)++(show l)++". "++(showd n gt)++",  "++"\n"++(showlist n xs)

-- some auxiliary functions for show ---

blanks :: (Eq t, Num t) => t -> [Char] -- returns a string of n blanks 
    
blanks 0  = ""
blanks n  = " "++(blanks (n-1))

lenint :: Interaction -> Int          -- returns the lenght of the string representation of an interaction
lenint (Interaction (Participant s1) (Participant s2)) = (length s1)+(length s2)+2

lenmes :: Message -> Int              -- returns the lenght of the string representation of a message
lenmes (Message s) = (length s)

lenp :: Participant -> Int            -- returns the lenght of the string representation of a participant
lenp   (Participant s) = (length s)

               

-- ======= Processes =======================

data Process =  Inact 
              | Mkinput Participant [(Message, Process)] 
              | MkOutput Participant [(Message, Process)]
    deriving (Eq)


instance Show Process where
     show proc = showdp 0 proc
        where
             showdp n Inact = "Inact"
             showdp n (Mkinput p [])          = "malformed process"
             showdp n (MkOutput p [])         = "malformed process"
             showdp n (Mkinput p [(m,proc)])  = (show p)++"?"++(show m)++"."++(showdp (n+(lenp p)+(lenmes m)+(if (n==0) then 3 else 5)) proc)
             showdp n (MkOutput p [(m,proc)]) = (show p)++"!"++(show m)++"."++(showdp (n+(lenp p)+(lenmes m)+(if (n==0) then 3 else 5)) proc)
             showdp n (Mkinput p ls)  = (show p)++"?"++"{"++"\n"++(showlistp (n+2+(lenp p)) ls)++"}"
             showdp n (MkOutput p ls) = (show p)++"!"++"{"++"\n"++(showlistp (n+2+(lenp p)) ls)++"}"
             showlistp n [(m,proc)]     = (blanks n)++(show m)++". "++(showdp n proc)
             showlistp n ((m,proc):xs)  = (blanks n)++(show m)++". "++(showdp n proc)++","++"\n"++(showlistp n xs)


                                     
-- ========== compliance judgments ======

data Judgment = Judgment Process Process Process
        deriving (Eq)
 
instance Show Judgment where
     show (Judgment proc1 proc2 proc3) = (show proc1)++" |- <"++(show proc2)++" , "++(show proc3)++">"


-- ======== compliance derivations =============

data Derivation =  Comp0 Judgment 
                 | CompOIL [Derivation] Judgment 
                 | CompIOL [Derivation] Judgment 
                 | CompOIR [Derivation] Judgment 
                 | CompIOR [Derivation] Judgment 
                 | CompOIA [Derivation] Judgment 
                 | CompIOA [Derivation] Judgment 
     deriving (Eq,Show)



