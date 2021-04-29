module Prove where

import Exception
import Term
import Trans
import Data.List
import Debug.Trace

prove (t,d) = let t' =  returnval (distill t EmptyCtx (free t) [] [] d)
              in  prove' [] (free t') t'

prove' fs fv (Free x) = False
prove' fs fv (Bound i) = False
prove' fs fv (Lambda x t) = let x' = renameVar fv x
                            in  prove' fs (x':fv) (concrete x' t)
prove' fs fv (Con c ts) = c == "True"
prove' fs fv (Case (Free x) bs) = all (\(c,xs,t) -> let fv' = renameVars fv xs
                                                        xs' = take (length xs) fv'
                                                    in  prove' (add x fs) fv' (foldr concrete t xs')) bs
prove' fs fv (Let x t u) = prove' fs fv t && prove' fs fv u
prove' fs fv (Unfold t u) = let f = renameVar (map fst fs) "f"
                                xs = free u
                            in  prove' ((f,(xs,[])):fs) fv (concrete f u)
prove' fs fv (Fold (Free f) u) = case lookup f fs of
                                    Nothing -> error "Unmatched fold"
                                    Just (xs,cs) -> not (null (xs `intersect` cs))

add x = map (\(f,(xs,cs)) -> (f,(xs,x:cs)))
