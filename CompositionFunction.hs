---------------------------------------------------------
-- This module implements the composition function and --
-- the function prune (prune cuts the branches of a       --
-- possibly infinite global type at a given level)      --
---------------------------------------------------------

module CompositionFunction where

import DataTypes 

-- --------- the composition function ---------

g :: Derivation      
     -> GlobalType
     -> GlobalType
     -> GlobalType
     -> Participant
     -> Participant
     -> Participant
     -> GlobalType
-- function g implements the function G defined in the proof of Theorem 5.8 
-- (the arguments ph, pv and ph are the name of interfaces names left implicit in the theorem)

g (Comp0 judg) gt1 gt2 gt3 ph pv pw  = gt1

g d@(CompOIL derlist judg) gt1@(MkGT (Interaction p1 p2) mglist1) gt2@(MkGT (Interaction p3 p4) mglist2) gt3 ph pv pw  
 | (p1,p4) == (ph,pv) = let 
                                    (ms,gts2)   = (unzip mglist2)
                                    (_,gts1aux) = (unzip mglist1)
                                    gts1        = (take (length gts2) gts1aux)
                                    rcalls      = [(g di gi ggi gt3 ph pv pw) | (di,gi,ggi)<- (zip3 derlist gts1 gts2)] 
                                    hatgts      = [(MkGT (Interaction pv ph)  [(m, (MkGT (Interaction ph p2) [(m,hatgi)]))]) | (m,hatgi)<- (zip ms rcalls)] 
                         in 
                            (MkGT (Interaction p3 p4) (zip ms hatgts))
  
 
 | (p1==ph)          = let           
                                   (ms,gts2)   = (unzip mglist2)
                                   rcalls      = [(g d gt1 gi gt3 ph pv pw) | gi<- gts2]
                        in  
                           (MkGT (Interaction p3 p4) (zip ms rcalls))
                            


 | otherwise         = let  
                                    (ms,gts1)   = (unzip mglist1)
                                    rcalls      = [(g d gi gt2 gt3 ph pv pw) | gi<- gts1]  
                        in  
                           (MkGT (Interaction p1 p2) (zip ms rcalls))

g d@(CompIOL derlist judg) gt1@(MkGT (Interaction p1 p2) mglist1) gt2@(MkGT (Interaction p3 p4) mglist2) gt3 ph pv pw  
 | (p2,p3) == (ph,pv) = let 
                                    (ms,gts1)   = (unzip mglist1)
                                    (_,gts1aux) = (unzip mglist2)
                                    gts2        = (take (length gts1) gts1aux)
                                    rcalls      = [(g di gi ggi gt3 ph pv pw) | (di,gi,ggi)<- (zip3 derlist gts1 gts2)] 
                                    hatgts      = [(MkGT (Interaction ph pv)  [(m, (MkGT (Interaction pv p4) [(m,hatgi)]))]) | (m,hatgi)<- (zip ms rcalls)] 
                         in 
                            (MkGT (Interaction p1 p2) (zip ms hatgts))
  
 
 | (p2==ph)          = let           
                                   (ms,gts2)   = (unzip mglist2)
                                   rcalls      = [(g d gt1 gi gt3 ph pv pw) | gi<- gts2]
                        in  
                           (MkGT (Interaction p3 p4) (zip ms rcalls))
                            


 | otherwise         = let  
                                    (ms,gts1)   = (unzip mglist1)
                                    rcalls      = [(g d gi gt2 gt3 ph pv pw) | gi<- gts1]  
                        in  
                           (MkGT (Interaction p1 p2) (zip ms rcalls))

g d@(CompOIR derlist judg) gt1@(MkGT (Interaction p1 p2) mglist1) gt2 gt3@(MkGT (Interaction p3 p4) mglist3) ph pv pw  
 | (p1,p4) == (ph,pw) = let 
                                    (ms,gts3)   = (unzip mglist3)
                                    (_,gts1aux) = (unzip mglist1)
                                    gts1        = (take (length gts3) gts1aux)
                                    rcalls      = [(g di gi gt2 ggi ph pv pw) | (di,gi,ggi)<- (zip3 derlist gts1 gts3)] 
                                    hatgts      = [(MkGT (Interaction pw ph)  [(m, (MkGT (Interaction ph p2) [(m,hatgi)]))]) | (m,hatgi)<- (zip ms rcalls)] 
                         in 
                            (MkGT (Interaction p3 p4) (zip ms hatgts))
  
 
 | (p1==ph)          = let           
                                   (ms,gts3)   = (unzip mglist3)
                                   rcalls      = [(g d gt1 gt2 gi ph pv pw) | gi<- gts3]
                        in  
                           (MkGT (Interaction p3 p4) (zip ms rcalls))
                            


 | otherwise         = let  
                                    (ms,gts1)   = (unzip mglist1)
                                    rcalls      = [(g d gi gt2 gt3 ph pv pw) | gi<- gts1]  
                        in  
                           (MkGT (Interaction p1 p2) (zip ms rcalls))

g d@(CompIOR derlist judg) gt1@(MkGT (Interaction p1 p2) mglist1) gt2 gt3@(MkGT (Interaction p3 p4) mglist3) ph pv pw  
 | (p2,p3) == (ph,pw) = let 
                                    (ms,gts1)   = (unzip mglist1)
                                    (_,gts3aux) = (unzip mglist3)
                                    gts3        = (take (length gts1) gts3aux)
                                    rcalls      = [(g di gi gt2 ggi ph pv pw) | (di,gi,ggi)<- (zip3 derlist gts1 gts3)] 
                                    hatgts      = [(MkGT (Interaction ph pw)  [(m, (MkGT (Interaction pw p4) [(m,hatgi)]))]) | (m,hatgi)<- (zip ms rcalls)] 
                         in 
                            (MkGT (Interaction p1 p2) (zip ms hatgts))
  
 
 | (p2==ph)          = let           
                                   (ms,gts3)   = (unzip mglist3)
                                   rcalls      = [(g d gt1 gt2 gi ph pv pw) | gi<- gts3]
                        in  
                           (MkGT (Interaction p3 p4) (zip ms rcalls))
                            


 | otherwise         = let  
                                    (ms,gts1)   = (unzip mglist1)
                                    rcalls      = [(g d gi gt2 gt3 ph pv pw) | gi<- gts1]  
                        in  
                           (MkGT (Interaction p1 p2) (zip ms rcalls))

g d@(CompOIA derlist judg) gt1@(MkGT (Interaction p1 p2) mglist1) gt2 gt3 ph pv pw  = 
                        let           
                                   (ms,gts1)   = (unzip mglist1)
                                   rcalls      = [(g di gi gt2 gt3 ph pv pw) | (di,gi)<- (zip derlist gts1)]
                        in  
                           (MkGT (Interaction p1 p2) (zip ms rcalls))


g d@(CompIOA derlist judg) gt1@(MkGT (Interaction p1 p2) mglist1) gt2 gt3 ph pv pw  = 
                        let           
                                   (ms,gts1)   = (unzip mglist1)
                                   rcalls      = [(g di gi gt2 gt3 ph pv pw) | (di,gi)<- (zip derlist gts1)]
                        in  
                           (MkGT (Interaction p1 p2) (zip ms rcalls))


-- ======== The function prune ===========

prune :: (Eq t, Num t) => t -> GlobalType -> GlobalType      -- cut the branches of a global type at level n

prune 0 gt   = Cut

prune n End = End

prune n (MkGT inter xs)    = (MkGT inter (pruneaux (n-1) xs)) 
                   where
                        pruneaux n []    = []
                        pruneaux n ((l,gt):xs) = (l,(prune n gt)):(pruneaux n xs)
