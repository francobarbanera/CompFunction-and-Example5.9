-------------------------------------------------------------------------------------------
-- This module implements the following functions:                                       --
-- g, returning the global type of a composition                                         --
-- prunegt, cutting the branches of a possibly infinite global type at a given level     --
-- pruneproc, cutting the branches of a possibly infinite process at a given level       --
-- gateways, returning the gateways for a composition from a given compliance derivation -- 
-- firstofthree, secondofthree, thirdofthree, returning the elements of a given triple   --
-------------------------------------------------------------------------------------------

module FunctionDefinitions where

import DataTypes 

-- ======== The composition function ==========

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

g d@(CompOA derlist judg) gt1@(MkGT (Interaction p1 p2) mglist1) gt2 gt3 ph pv pw  = 
                        let           
                                   (ms,gts1)   = (unzip mglist1)
                                   rcalls      = [(g di gi gt2 gt3 ph pv pw) | (di,gi)<- (zip derlist gts1)]
                        in  
                           (MkGT (Interaction p1 p2) (zip ms rcalls))


g d@(CompIA derlist judg) gt1@(MkGT (Interaction p1 p2) mglist1) gt2 gt3 ph pv pw  = 
                        let           
                                   (ms,gts1)   = (unzip mglist1)
                                   rcalls      = [(g di gi gt2 gt3 ph pv pw) | (di,gi)<- (zip derlist gts1)]
                        in  
                           (MkGT (Interaction p1 p2) (zip ms rcalls))


-- ======== The pruning functions ===========

prunegt :: (Eq t, Num t) => t -> GlobalType -> GlobalType      -- cut the branches of a global type at level n

prunegt 0 gt   = Cut

prunegt n End = End

prunegt n (MkGT inter xs)    = (MkGT inter (prunegtaux (n-1) xs)) 
                     where
                          prunegtaux n []    = []
                          prunegtaux n ((l,gt):xs) = (l,(prunegt n gt)):(prunegtaux n xs)

pruneproc 0 gt    = Cutp

pruneproc n Inact = Inact

pruneproc n (MkInput pn xs)    = (MkInput pn (pruneprocaux (n-1) xs)) 
                     where
                          pruneprocaux n []    = []
                          pruneprocaux n ((l,proc):xs) = (l,(pruneproc n proc)):(pruneprocaux n xs)

pruneproc n (MkOutput pn xs)    = (MkOutput pn (pruneprocaux (n-1) xs)) 
                     where
                          pruneprocaux n []    = []
                          pruneprocaux n ((l,proc):xs) = (l,(pruneproc n proc)):(pruneprocaux n xs)

-- ========= The gateways function ===========

gateways
  :: Derivation
     -> Participant
     -> Participant
     -> Participant
     -> (Process, Process, Process)  -- returns the gateways induced by a derivation of compliance for the processes for the participant names given as arguments ph pv pw

gateways (Comp0 judg) ph pv pw           = (Inact,Inact,Inact)
gateways (CompOIL derlist judg) ph pv pw = (hatH,hatV,hatW)
                           where
                                 (Judgment (MkOutput nameproc1 mps1) (MkInput nameproc2 mps2) _) = judg   
                                 (ms2,ps2)   = unzip mps2
                                 (_,ps1aux)  = unzip mps1
                                 ps1         = (take (length ps2) ps1aux)
                                 rcalls      = [(gateways di ph pv pw) | di<- derlist]
                                 (hatHs,hatVs,hatWs) =  (unzip3 rcalls)
                                 hatH    = (MkInput pv (zip ms2 [(MkOutput nameproc1 [(mi,hatHi)]) | (mi,hatHi)<- (zip ms2 hatHs)]))
                                 hatV    = (MkInput nameproc2 (zip ms2 [(MkOutput ph [(mi,hatVi)]) | (mi,hatVi)<- (zip ms2 hatVs)]))
                                 (_,_,hatW) = head rcalls

gateways (CompIOL derlist judg) ph pv pw = (hatH,hatV,hatW)
                           where
                                 (Judgment (MkInput nameproc1 mps1) (MkOutput nameproc2 mps2) _) = judg   
                                 (ms1,ps1)   = unzip mps1
                                 (_,ps2aux)  = unzip mps1
                                 ps2         = (take (length ps1) ps2aux)
                                 rcalls  = [(gateways di ph pv pw) | di<- derlist]
                                 (hatHs,hatVs,hatWs) =  (unzip3 rcalls)
                                 hatH    = (MkInput nameproc1 (zip ms1 [(MkOutput pv [(mi,hatHi)]) | (mi,hatHi)<- (zip ms1 hatHs)]))
                                 hatV    = (MkInput ph (zip ms1 [(MkOutput nameproc2 [(mi,hatVi)]) | (mi,hatVi)<- (zip ms1 hatVs)]))
                                 (_,_,hatW) = head rcalls

gateways (CompOIR derlist judg) ph pv pw = (hatH,hatV,hatW)
                           where
                                 (Judgment (MkOutput nameproc1 mps1) _ (MkInput nameproc3 mps3)) = judg   
                                 (ms3,ps3)   = unzip mps3
                                 (_,ps1aux)  = unzip mps1
                                 ps1         = (take (length ps3) ps1aux)
                                 rcalls      = [(gateways di ph pv pw) | di<- derlist]
                                 (hatHs,hatVs,hatWs) =  (unzip3 rcalls)
                                 hatH    = (MkInput pw (zip ms3 [(MkOutput nameproc1 [(mi,hatHi)]) | (mi,hatHi)<- (zip ms3 hatHs)]))
                                 hatW    = (MkInput nameproc3 (zip ms3 [(MkOutput ph [(mi,hatWi)]) | (mi,hatWi)<- (zip ms3 hatWs)]))
                                 (_,hatV,_) = head rcalls

gateways (CompIOR derlist judg) ph pv pw = (hatH,hatV,hatW)
                           where
                                 (Judgment (MkInput nameproc1 mps1) _ (MkOutput nameproc3 mps2)) = judg   
                                 (ms1,ps1)   = unzip mps1
                                 (_,ps3aux)  = unzip mps1
                                 ps3         = (take (length ps1) ps3aux)
                                 rcalls  = [(gateways di ph pv pw) | di<- derlist]
                                 (hatHs,hatVs,hatWs) =  (unzip3 rcalls)
                                 hatH    = (MkInput nameproc1 (zip ms1 [(MkOutput pw [(mi,hatHi)]) | (mi,hatHi)<- (zip ms1 hatHs)]))
                                 hatW    = (MkInput ph (zip ms1 [(MkOutput nameproc3 [(mi,hatWi)]) | (mi,hatWi)<- (zip ms1 hatWs)]))
                                 (_,hatV,_) = head rcalls

gateways (CompOA derlist judg) ph pv pw = (hatH,hatV,hatW)
                           where
                                 (Judgment (MkOutput nameproc1 mps1) _ _) = judg
                                 (ms1,ps1)   = unzip mps1
                                 rcalls      = [(gateways di ph pv pw) | di<- derlist]
                                 (hatHs,hatVs,hatWs) =  (unzip3 rcalls)
                                 hatH    = (MkOutput nameproc1 (zip ms1 hatHs))
                                 (_,hatV,hatW) = head rcalls
                                     
gateways (CompIA derlist judg) ph pv pw = (hatH,hatV,hatW)
                           where
                                 (Judgment (MkInput nameproc1 mps1) _ _) = judg
                                 (ms1,ps1)   = unzip mps1
                                 rcalls      = [(gateways di ph pv pw) | di<- derlist]
                                 (hatHs,hatVs,hatWs) =  (unzip3 rcalls)
                                 hatH    = (MkInput nameproc1 (zip ms1 hatHs))
                                 (_,hatV,hatW) = head rcalls

firstofthree :: (a, b, c) -> a
firstofthree (x,y,z) = x

secondofthree :: (a, b, c) -> b
secondofthree (x,y,z) = y 

thirdofthree :: (a, b, c) -> c
thirdofthree (x,y,z) = z

