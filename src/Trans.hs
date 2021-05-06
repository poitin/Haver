module Trans where

import Term
import Exception
import Prelude hiding ((<>))
import Data.Maybe
import Data.List
import Debug.Trace

dist (t,d) = let t' =  returnval (distill t EmptyCtx (free t) [] [] d)
             in  residualise (t',[])

distill (Free x) (CaseCtx k bs) fv m1 m2 d = do
                                             bs' <- mapM (\(c,xs,t) -> let t' = place t k
                                                                           fv' = renameVars fv xs
                                                                           xs' = take (length xs) fv'
                                                                           u = foldr concrete (subst (Con c (map Free xs')) (abstract t' x)) xs'
                                                                       in do
                                                                          u' <- distill u EmptyCtx fv' m1 m2 d
                                                                          return (c,xs,foldl abstract u' xs')) bs
                                             return (Case (Free x) bs')
distill (Free x) k fv m1 m2 d = distillCtx (Free x) k fv m1 m2 d
distill (Lambda x t) EmptyCtx fv m1 m2 d = let x' = renameVar fv x
                                           in do
                                              t' <- distill (concrete x' t) EmptyCtx (x':fv) m1 m2 d
                                              return (Lambda x (abstract t' x'))
distill (Lambda x t) (ApplyCtx k u) fv m1 m2 d = distill (subst u t) k fv m1 m2 d
distill (Lambda x t) (CaseCtx k bs) fv m1 m2 d = error "Unapplied function in case selector"
distill (Con c ts) EmptyCtx fv m1 m2 d = do
                                         ts' <- mapM (\t -> distill t EmptyCtx fv m1 m2 d) ts
                                         return (Con c ts')
distill (Con c ts) (ApplyCtx k u) fv m1 m2 d = error ("Constructor application is not saturated: "++show (place (Con c ts) (ApplyCtx k u)))
distill (Con c ts) (CaseCtx k bs) fv m1 m2 d = case find (\(c',xs,t) -> c==c' && length xs == length ts) bs of
                                                  Nothing -> error ("No matching pattern in case for term:\n\n"++show (Case (Con c ts) bs))
                                                  Just (c',xs,t) -> distill (foldr subst t ts) k fv m1 m2 d
distill (Apply t u) k fv m1 m2 d = distill t (ApplyCtx k u) fv m1 m2 d
distill (Fun f) k fv m1 m2 d = fold1 (place (Fun f) k) fv m1 m2 d
distill (Case t bs) k fv m1 m2 d = distill t (CaseCtx k bs) fv m1 m2 d
distill (Let x t u) k fv m1 m2 d = let x' = renameVar fv x
                                   in do
                                      t' <- distill t EmptyCtx fv m1 m2 d
                                      u' <- distill (concrete x' u) k (x':fv) m1 m2 d
                                      return (Let x t' (abstract u' x'))

distillCtx t EmptyCtx fv m1 m2 d = return t
distillCtx t (ApplyCtx k u) fv m1 m2 d = do
                                         u' <- distill u EmptyCtx fv m1 m2 d
                                         distillCtx (Apply t u') k fv m1 m2 d
distillCtx t (CaseCtx k bs) fv m1 m2 d = do
                                         bs' <- mapM (\(c,xs,t) -> let fv' = renameVars fv xs
                                                                       xs' = take (length xs) fv'
                                                                   in do
                                                                      t' <- distill (foldr concrete t xs') k fv' m1 m2 d
                                                                      return (c,xs,foldl abstract t' xs')) bs
                                         return (Case t bs')

fold1 t fv m1 m2 d = case find (\(f,t') -> isInst t' t) m1 of
                        Just (f,t') -> let s = head (inst t' t)
                                           u = foldl Apply (Fun f) (map Free (free t'))
                                       in  return (Fold (instantiate s u) t)
                        Nothing -> case find (\(f,t') -> isEmbed t' t) m1 of
                                      Just (f,t') -> throw (f,t)
                                      Nothing -> let f = renameVar (map fst m1++map fst m2) "f"
                                                     u = foldl Apply (Fun f) (map Free (free t))
                                                     handler (f',t') = if   f==f'
                                                                       then let r = head (embedding t t')
                                                                                (u,s1,s2) = generalise t (rename r t')
                                                                            in  do
                                                                                u' <- distill u EmptyCtx fv m1 m2 d
                                                                                fold2 u' fv s1 m1 m2 d
                                                                       else throw (f',t')
                                                 in  do 
                                                     u' <- handle (distill (unfold(t,d)) EmptyCtx fv ((f,t):m1) m2 d) handler
                                                     if Fun f `elem` folds u' then fold2 (Unfold u u') fv [] m1 m2 d else return u'

fold2 t fv s m1 m2 d  = let t' = instantiate s t
                        in  case find (\(f,u) -> isInst u t') m2 of
                               Just (f,u) -> let s'' = head (inst u t')
                                                 u' = foldl Apply (Fun f) (map Free (free u))
                                             in  return (Fold (instantiate s'' u') t')
                               Nothing -> case find (\(f,u) -> isEmbed u t') m2 of
                                             Just (f,u) -> throw (f,t)
                                             Nothing -> let f = renameVar (map fst m1 ++ map fst m2) "f"
                                                            u = foldl Apply (Fun f) (map Free (free t'))
                                                            handler (f',t') = if   f==f'
                                                                              then let r = head (embedding t t')
                                                                                       (u,s1,s2) = generalise t (rename r t')
                                                                                       (u',d') = residualise (makeLet s1 u,d)
                                                                                   in  distill (instantiate s u') EmptyCtx fv m1 m2 d'
                                                                              else throw (f',t')
                                                            (u',d') = residualise (t,d)
                                                        in  do 
                                                            u'' <- handle (distill (unfold(instantiate s u',d')) EmptyCtx fv m1 ((f,t'):m2) d') handler
                                                            return (if Fun f `elem` folds u'' then Unfold u u'' else u'')

