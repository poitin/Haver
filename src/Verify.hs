module Verify where

import Exception
import Term
import Trans
import Data.List
import Debug.Trace

prove (t,d) = let t' =  returnval (distill t EmptyCtx (free t) [] [] d)
              in  prove' t' (free t') []

prove' (Free x) fv m = False
prove' (Bound i) fv m = False
prove' (Lambda x t) fv m = let x' = renameVar fv x
                           in  prove' (concrete x' t) (x':fv) m
prove' (Con c ts) fv m = c == "True"
prove' (Case (Free x) bs) fv m = all (\(c,xs,t) -> let fv' = renameVars fv xs
                                                       xs' = take (length xs) fv'
                                                   in  prove' (foldr concrete t xs') fv' (add x m)) bs
prove' (Let x t u) fv m = prove' t fv m && prove' u fv m
prove' (Unfold t u) fv m = prove' u fv ((t,[]):m)
prove' (Fold t u) fv m = case find (\(t',cs) -> isInst t' t) m of
                              Nothing -> prove' u fv m
                              Just (t',cs) -> not (null (free t' `intersect` cs))

add x = map (\(t,cs) -> (t,x:cs))
